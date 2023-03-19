;;; transitive-closure.el -*- lexical-binding: t -*-
;;; Efficient implementation of transitive closure on a graph of symbols
;;;  Based on Nuutila's thesis - https://www.cs.hut.fi/~enu/thesis.pdf, page 62
;;; Interface
;;; (tc-transitive-closure nodes edges) => tc--graph structures
;;; (tc-graph-scc tc--graph node) => the equivalence class of nodes for node
;;; (tc-graph-successors tc-graph node) => list of nodes reachable from node
;;; (tc-graph-ordering tc-graph) =>
;;;     array of lists of nodes consistent with partial ordering
;;;     i.e nodes in list 0 have no dependencies
;;;         nodes in list 1 only have dependencies in list 0
;;;         nodes in list 2 only have dependencies in list 0 or 1
;;;         etc.

(eval-when-compile (require 'cl-lib))
(eval-when-compile (require 'cl-macs))
(require 'avl-tree-core)

(cl-defstruct tc--graph
  nodes edges roots reachable node->idx node-ordering
  idx->node idx->scc idx->successors
  scc-edges scc->order scc-ordering
  scc->rep scc->nodes scc->succs)

(defvar tc--edges nil)
(defvar tc--nodes nil)
(defvar tc--roots nil)
(defvar tc--size-nodes nil)
(defvar tc--node->idx nil)
(defvar tc--idx->visited nil)
(defvar tc--idx->node nil)
(defvar tc--idx->root nil)
(defvar tc--idx->self-edge nil)
(defvar tc--idx->height nil)
(defvar tc--idx->scc nil)
(defvar tc--idx->successors nil)
(defvar tc--scc->rep nil)
(defvar tc--sccs nil)
(defvar tc--scc-edges nil)
(defvar tc--scc->nodes nil)
(defvar tc--visit-idx nil)
(defvar tc--cstack nil)
(defvar tc--vstack nil)
(defvar tc--idx nil)
(defvar tc--root nil)
(defvar tc--scc->scc-node nil)
(defvar tc--scc->successors nil)
(defvar tc--scc-count nil)
(defvar tc--cstack-height nil)
(defvar tc--scc-succs nil)
(defvar tc--scc-succ-gens nil)
(defvar tc--scc->node-successor-sets nil)
(defvar tc--scc->order nil)
(defvar tc--scc-ordering nil)
(defvar tc--reachable-nodes nil)

;;;  nodes is a list of symbols
;;;  edges is an alist specifying directed graph edges from each node

(defun tc--init (nodes edges roots)
  "Initialize state variables for transitive closure calculation"
  (setq tc--edges edges
        tc--nodes nodes
        tc--roots roots
        tc--size-nodes (length tc--nodes)
        tc--reachable-nodes nil
        tc--idx->node (make-vector tc--size-nodes nil)
        tc--node->idx (make-hash-table :size tc--size-nodes))
  (let ((ls nodes)
        (i 0)
        (v nil))
    (while ls
      (setq v (pop ls))
      (puthash v i tc--node->idx)
      (aset tc--idx->node i v)
      (setq i (1+ i))))
  (setq tc--idx->visited (make-vector tc--size-nodes nil)
        tc--idx->root (make-vector tc--size-nodes nil)
        tc--idx->self-edge (make-vector tc--size-nodes nil)
        tc--idx->scc (make-vector tc--size-nodes nil)
        tc--idx->height (make-vector tc--size-nodes nil)
        tc--sccs (make-vector tc--size-nodes nil)
        tc--scc->rep (make-vector tc--size-nodes nil)
        tc--scc-edges nil
        tc--idx->successors (make-vector (length tc--nodes) nil)
        tc--scc->node-successor-sets nil
        ;; this is wasteful of space, but a convenient method for creating
        ;; component nodes
        tc--scc->scc-node (make-vector (length tc--nodes) nil)
        tc--scc->successors (make-vector (length tc--nodes) nil)
        tc--scc->order (make-vector (length tc--nodes) -1)
        tc--scc-ordering nil
        tc--scc-count 0
        tc--cstack nil
        tc--vstack nil
        tc--visit-idx 0
        tc--cstack-height 0
        tc--scc-succs (make-bool-vector (length tc--nodes) nil)
        tc--scc-succ-gens (make-bool-vector (length tc--nodes) nil)))

(defun tc--get-node-index (v)
  (gethash v tc--node->idx))
(defun tc--make-scc-set ()
  (avl-tree-create #'<))
(defun tc--scc-< (a b)
  (and (avl-tree-member-p
        (aref tc--scc->successors a)
        b)
       (/= a b)))
(defun tc--scc-<= (a b)
  (or (= a b)
      (avl-tree-member-p
       (aref tc--scc->successors a)
       b)))

(defun tc--scc-set-null (ss)
  (avl-tree-empty ss))
(defun tc--scc-set-member (elt ss)
  (avl-tree-member-p ss elt))
(defun tc--scc-set-del (elt ss)
  (avl-tree-delete ss elt)
  ss)
(defun tc--scc-set-add (elt ss)
  (avl-tree-enter ss elt)
  ss)
(defun tc--scc-set->list (ss)
  (avl-tree-flatten ss))
(defun tc--scc-set-seq (ss)
  (avl-tree-stack ss))
(defun tc--scc-set-seq-null (ss)
  (avl-tree-stack-empty-p ss))
(defun tc--scc-set-seq-first (ss)
  (avl-tree-stack-first ss))
(defun tc--scc-set-seq-pop (ss)
  (avl-tree-stack-pop ss))
(defun tc--scc-set-mapcar (f ss)
  (avl-tree-mapcar f ss))
(defun tc--scc-set-mapcan (f ss)
  (apply #'nconc (avl-tree-mapcar f ss)))
(defun tc--scc-set-mapc (f ss)
  (avl-tree-mapc f ss))

(defun tc--scc-set-union (ss0 &rest ss-rest)
  (let ((acc (avl-tree-copy ss0))
        idxs)
    (while ss-rest
      (setq idxs (tc--scc-set-seq (car ss-rest)))
      (setq ss-rest (cdr ss-rest))
      (while (not (tc--scc-set-seq-null idxs))
        (tc--scc-set-add (tc--scc-set-seq-pop idxs)
                         acc)))
    acc))

(defun tc--scc-set-union-accumulate (acc ss1)
  (let ((idxs (tc--scc-set-seq ss1)))
    (while (not (tc--scc-set-seq-null idxs))
      (tc--scc-set-add (tc--scc-set-seq-pop idxs)
                       acc)))
  acc)


(defun tc--add-to-meet-generators (d gens)
  (let ((gs (tc--scc-set-seq gens))
        (to-remove nil))
    (while (and (> d -1) (not (tc--scc-set-seq-null gs)))
      (let ((u (tc--scc-set-seq-pop gs)))
        (cond
         ((tc--scc-<= u d)  (setq d -1))
         ((tc--scc-< d u)   (push u to-remove)))))
    (when (and (< d 0)
               to-remove)
      (error "Transitive closure: Inconsistent topological sorted successor components"))
    (when to-remove
      (mapc (lambda (x) (tc--scc-set-del x gens)) to-remove))
    (when (>= d 0)
      (tc--scc-set-add d gens)))
  gens)

(defun tc--stack-tc-visit (v v-idx v-visited w)
  (if (eq w v)
      (aset tc--idx->self-edge v-idx t)
    (let ((w-idx (tc--get-node-index w))
          fwd-edge w-visited)
      ;; v -> w is a forward edge if
      ;;    (a) w has already been visited, and
      ;;    (b) v is visited before w
      (setq w-visited (aref tc--idx->visited w-idx))
      (when (and w-visited
                 (< v-visited w-visited))
        (setq fwd-edge t))
      (unless w-visited
        (tc--stack-tc w w-idx)
        (setq w-visited (aref tc--idx->visited w-idx)))
      (let ((w-scc (aref tc--idx->scc w-idx)))
        (cond
         ((null w-scc)
          (aset tc--idx->root v-idx
                (min (aref tc--idx->root v-idx)
                     (aref tc--idx->root w-idx))))
         ((not fwd-edge)
          (push w-scc tc--cstack)
          (setq tc--cstack-height (1+ tc--cstack-height))))))))

(defun tc--stack-tc-determine-meet-generators (h0)
  (let ((gens (tc--make-scc-set))
        d)
    (while (> tc--cstack-height h0)
      (setq d (pop tc--cstack)
            tc--cstack-height (1- tc--cstack-height))
      ;; skip if this component has already been processed
      (unless (aref tc--scc-succs d)
        ;; see if d is in successors of existing
        ;; component or vice versa
        (aset tc--scc-succs d t)
        (setq gens
              (tc--add-to-meet-generators d gens))))
    gens))

(defun tc--stack-tc-collect-scc-succs (c c-succs gens)
  (let ((gs (tc--scc-set-seq gens))
        (order -1)
        d d-succs)
    (while (not (tc--scc-set-seq-null gs))
      (setq d (tc--scc-set-seq-pop gs))
      (setq order (max order (aref tc--scc->order d)))
      (setq d-succs (aref tc--scc->successors d))
      (setq c-succs
            (tc--scc-set-add d c-succs))
      (setq c-succs
            (tc--scc-set-union-accumulate c-succs d-succs)))
    (aset tc--scc->order c (1+ order)))
  (aset tc--scc->successors c c-succs)
  c-succs)


(defun tc--stack-tc-collect-scc (v-idx)
  (let ((c tc--scc-count)
        ;; note c-succs is a set of scc indices, not indices of original nodes
        (c-succs (tc--make-scc-set))
        c-elts gens)
    (aset tc--scc->rep c v-idx)
    (fillarray tc--scc-succs nil)
    (setq tc--scc-count (1+ tc--scc-count))
    (when (or (/= (car tc--vstack) v-idx)
              (aref tc--idx->self-edge v-idx))
      (tc--scc-set-add c c-succs))
    (setq gens
          (tc--stack-tc-determine-meet-generators
           (aref tc--idx->height v-idx)))
    (push `(,c ,@(tc--scc-set->list gens)) tc--scc-edges)
    (setq c-succs
          (tc--stack-tc-collect-scc-succs c c-succs gens))
    ;; Finally determine members of c
    (let ((w-idx (pop tc--vstack)))
      (aset tc--idx->scc w-idx c)
      (push w-idx c-elts)
      (while (/= w-idx v-idx)
        (setq w-idx (pop tc--vstack))
        (aset tc--idx->scc w-idx c)
        (push w-idx c-elts)))
    (aset tc--sccs c c-elts)))

(defun tc--stack-tc (v v-idx)
  "Compute the transitive closure of tc--graph"
  (when (aref tc--idx->visited v-idx)
    (error "Visiting %S %S twice" v v-idx))
  (aset tc--idx->visited v-idx tc--visit-idx )
  (setq tc--visit-idx (1+ tc--visit-idx))
  (aset tc--idx->root v-idx v-idx)
  (aset tc--idx->height v-idx tc--cstack-height)
  (push v-idx tc--vstack)
  (let ((succs (assq v tc--edges))
        (v-visited (aref tc--idx->visited v-idx)))
    (when succs
      (pop succs))
    (while succs
      (tc--stack-tc-visit v v-idx v-visited (pop succs))))
  (when (= v-idx (aref tc--idx->root v-idx))
    (tc--stack-tc-collect-scc v-idx)))

(defun tc-transitive-closure (nodes edges &optional roots)
  "Compute the transitive closure of tc--graph.
Returns a tc-graph structure."
  (unless roots
    (setq roots nodes))
  (tc--init nodes edges roots)
  (let ((ls roots)
        v v-idx)
    (while ls
      (setq v (pop ls))
      (setq v-idx (tc--get-node-index v))
      (unless (aref tc--idx->visited v-idx)
        (tc--stack-tc v v-idx))))
  (setq tc--scc->rep (make-vector tc--scc-count nil))
  (let ((i 0)
        (max-order 0)
        (o -1)
        (scc->order (make-vector tc--scc-count nil))
        (scc->rep (make-vector tc--scc-count nil))
        (scc->nodes (make-vector tc--scc-count nil)))
    (while (< i tc--scc-count)
      (aset scc->nodes i (aref tc--sccs i))
      (aset scc->order i (aref tc--scc->order i))
      (setq max-order (max max-order (aref scc->order i)))
      (aset scc->rep i (aref tc--scc->rep i))
      (setq i (1+ i)))
    (setq tc--scc-ordering (make-vector (1+ max-order) nil)
          i 0)
    (while (< i tc--scc-count)
      (setq o (aref scc->order i))
      (aset tc--scc-ordering
            o
            (cons i
                  (aref tc--scc-ordering o)))
      (setq i (1+ i)))
    (setq tc--scc->rep scc->rep)
    (setq tc--scc->order scc->order)
    (setq tc--sccs scc->nodes)
    (setq i (1- tc--size-nodes))
    (while (>= i 0)
      (when (aref tc--idx->visited i)
        (push (aref tc--idx->node i) tc--reachable-nodes))
      (setq i (1- i))))
  (make-tc--graph
   :nodes tc--nodes
   :edges tc--edges
   :roots tc--roots
   :reachable tc--reachable-nodes
   :node->idx tc--node->idx
   :idx->node tc--idx->node
   :idx->scc tc--idx->scc
   :idx->successors tc--idx->successors
   :scc-edges tc--scc-edges
   :scc->rep tc--scc->rep
   :scc->order tc--scc->order
   :scc-ordering tc--scc-ordering
   :scc->nodes tc--sccs
   :scc->succs tc--scc->successors))


(defun tc-graph-scc (tcg v)
  (unless (memq v (tc--graph-nodes tcg))
    (error "%S is not a node of the graph" v))
  (let ((v-idx (gethash v (tc--graph-node->idx tcg)))
        (idx->node (tc--graph-idx->node tcg))
        (idx->scc (tc--graph-idx->scc tcg))
        (scc->nodes (tc--graph-scc->nodes tcg)))
    (let ((scc (mapcar (lambda (idx) (aref idx->node idx))
                       (aref scc->nodes
                             (aref idx->scc v-idx)))))
      scc)))

(defun tc-graph-reachable (tcg &optional v)
  (if (null v)
      (tc--graph-reachable tcg)
    (let ((v-idx (gethash v (tc--graph-node->idx tcg)))
          (idx->node (tc--graph-idx->node tcg))
          (idx->scc (tc--graph-idx->scc tcg))
          (scc->succs (tc--graph-scc->succs tcg))
          (scc->nodes (tc--graph-scc->nodes tcg))
          (idx->successors (tc--graph-idx->successors tcg))
          scc scc-succs v-succs)
      (unless (aref idx->successors v-idx)
        (setq scc (aref idx->scc v-idx))
        (setq scc-succs (aref scc->succs scc))
        (setq v-succs
              (tc--scc-set-mapcan
               (lambda (c)
                 (mapcar (lambda (idx)
                           (aref idx->node idx))
                         (aref scc->nodes c)))
               scc-succs))
        (aset idx->successors v-idx v-succs))
      (aref idx->successors v-idx))))

(defun tc-graph-order (tcg v)
  (let ((v-idx (gethash v (tc--graph-node->idx tcg)))
        (idx->scc (tc--graph-idx->scc tcg))
        (scc->order (tc--graph-scc->order tcg)))
    (aref scc->order
          (aref idx->scc v-idx))))

(defun tc-graph-ordering (tcg)
  (let ((o (tc--graph-node-ordering tcg)))
    (unless o
      (setq o (copy-sequence (tc--graph-scc-ordering tcg)))
      (let ((n (length o))
            (scc->nodes (tc--graph-scc->nodes tcg))
            (idx->node (tc--graph-idx->node tcg))
            (i 0))
        (while (< i n)
          (aset o i
                (mapcan
                 (lambda (scc)
                   (mapcar (lambda (idx)
                             (aref idx->node idx))
                           (aref scc->nodes scc)))
                 (aref o i)))
          (setq i (1+ i))))
      (setf (tc--graph-node-ordering tcg) o))
    o))

(defun tc-invert-edges (nodes edges)
  (let ((inv-map (make-hash-table :size (length nodes)))
        (inv-als nil)
        (ls edges)
        to from tols fromls)
    (while ls
      (setq tols (pop ls))
      (setq from (pop tols))
      (while tols
        (setq to (pop tols))
        (setq fromls (gethash to inv-map nil))
        (push from fromls)
        (puthash to fromls inv-map)))
    (maphash (lambda (k v)
               (push `(,k . ,v) inv-als))
             inv-map)
    inv-als))

;;  specified graph provides reverse of desired ordering wrt specified roots
(defun tc-reverse-rooted-graph (nodes edges &optional roots)
  (let (inv-edges
        tcg-fwd tcg-back
        reachable-nodes reachable reachable-edges)
    (setq inv-edges (tc-invert-edges nodes edges))
    (setq tcg-fwd (tc-transitive-closure nodes inv-edges roots))
    (setq reachable-nodes (tc--graph-reachable tcg-fwd))
    (setq reachable (make-hash-table :size (length reachable-nodes)))
    (mapc (lambda (v) (puthash v t reachable)) reachable-nodes)
    (setq reachable-edges
          (mapcan (lambda (apr)
                    (let ((from (car apr))
                          (tols (cdr apr))
                          result)
                      (when (gethash from reachable nil)
                        (setq result
                              `((,from
                                 ,@(seq-filter
                                    (lambda (to)
                                      (gethash to reachable nil))
                                    tols)))))
                      result))
                  edges))
    (setq tcg-back (tc-transitive-closure reachable-nodes reachable-edges))
    tcg-back))


;;; Tests

;; (defvar tst-nodes nil)
;; (setq tst-nodes '(a b c d e))
;; (defvar tst-edges0 nil)
;; (setq tst-edges0 '())
;; (defvar tst-edges1 nil)
;; (setq tst-edges1 '((a)
;;                      (b)
;;                      (c)
;;                      (d)
;;                      (e)))
;; (defvar tst-edges2 nil)
;; (setq tst-edges2 '((a)
;;                       (b a)
;;                       (c b)
;;                       (d c)
;;                       (e d)))
;; (defvar tst-edges3 nil)
;; (setq tst-edges3 '((a b)
;;                    (b c)
;;                    (c d)
;;                    (d e)
;;                    (e)))
;; (defvar tst-edges4 nil)
;; (setq tst-edges4 '((a a)
;;                    (b a b c)
;;                    (c d)
;;                    (d a b)
;;                    (e e b)))
;; (defvar tst-edges5 nil)
;; (setq tst-edges5 '((a e)
;;                    (b d)
;;                    (c a)
;;                    (d e)
;;                    (e)))

;; (defvar test-tc0 nil)
;; (setq test-tc0 (tc-transitive-closure tst-nodes tst-edges0))
;; (defvar test-tc1 nil)
;; (setq test-tc1 (tc-transitive-closure tst-nodes tst-edges1))
;; (defvar test-tc2 nil)
;; (setq test-tc2 (tc-transitive-closure tst-nodes tst-edges2))
;; (tc-graph-scc test-tc2 'a)
;; (tc-graph-scc test-tc2 'b)
;; (tc-graph-scc test-tc2 'c)
;; (tc-graph-scc test-tc2 'd)
;; (tc-graph-scc test-tc2 'e)
;; (tc-graph-successors test-tc2 'a)
;; (tc-graph-successors test-tc2 'b)
;; (tc-graph-successors test-tc2 'c)
;; (tc-graph-successors test-tc2 'd)
;; (tc-graph-successors test-tc2 'e)
;; (defvar test-tc3 nil)
;; (setq test-tc3 (tc-transitive-closure tst-nodes tst-edges3))
;; (tc-graph-scc test-tc3 'a)
;; (tc-graph-scc test-tc3 'b)
;; (tc-graph-scc test-tc3 'c)
;; (tc-graph-scc test-tc3 'd)
;; (tc-graph-scc test-tc3 'e)
;; (tc-graph-successors test-tc3 'a)
;; (tc-graph-successors test-tc3 'b)
;; (tc-graph-successors test-tc3 'c)
;; (tc-graph-successors test-tc3 'd)
;; (tc-graph-successors test-tc3 'e)
;; (defvar test-tc4 nil)
;; (setq test-tc4 (tc-transitive-closure tst-nodes tst-edges4))
;; (tc-graph-scc test-tc4 'a)
;; (tc-graph-scc test-tc4 'b)
;; (tc-graph-scc test-tc4 'c)
;; (tc-graph-scc test-tc4 'd)
;; (tc-graph-scc test-tc4 'e)
;; (tc-graph-successors test-tc4 'a)
;; (tc-graph-successors test-tc4 'b)
;; (tc-graph-successors test-tc4 'c)
;; (tc-graph-successors test-tc4 'd)
;; (tc-graph-successors test-tc4 'e)
;; (defvar test-tc5 nil)
;; (setq test-tc5 (tc-transitive-closure tst-nodes tst-edges5))
;; (tc-graph-scc test-tc5 'a)
;; (tc-graph-scc test-tc5 'b)
;; (tc-graph-scc test-tc5 'c)
;; (tc-graph-scc test-tc5 'd)
;; (tc-graph-scc test-tc5 'e)
;; (tc-graph-successors test-tc5 'a)
;; (tc-graph-successors test-tc5 'b)
;; (tc-graph-successors test-tc5 'c)
;; (tc-graph-successors test-tc5 'd)
;; (tc-graph-successors test-tc5 'e)
;; (defvar test-tc5-rev nil)
;; (setq test-tc5-rev (tc-reverse-rooted-graph tst-nodes tst-edges5 '(e)))
;; (tc-graph-ordering test-tc5-rev)
;; (defvar test-tc5-rev2 nil)
;; (setq test-tc5-rev2 (tc-reverse-rooted-graph tst-nodes tst-edges5 '(d a)))
;; (tc-graph-ordering test-tc5-rev2)
