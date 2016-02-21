;; coq.el --- Coq mode editing commands for Emacs

;; Marco Maggesi, 2002-08-20
;; Born as a modified version of coq.el by Jean-Christophe Filliatre

;; This code is unstable: should work just fine under Gnu Emacs 20 and
;; 21, but I plan to make incompatible changes in the future.

(defvar coq-mode-map nil
  "Keymap used in Coq mode.")
(if coq-mode-map
    ()
  (setq coq-mode-map (make-sparse-keymap))
  (define-key coq-mode-map "\t" 'coq-indent-command)
  (define-key coq-mode-map "\M-\t" 'coq-unindent-command)
  (define-key coq-mode-map "\C-c\C-c" 'compile)
  (define-key coq-mode-map [(shift right)] 'coq-forward-vernac)
  (define-key coq-mode-map [(shift left)] 'coq-backward-vernac)
  (define-key coq-mode-map [(shift home)] 'coq-beginning-of-vernac)
  (define-key coq-mode-map [(shift end)] 'coq-end-of-vernac)
  (define-key coq-mode-map [f2] 'coq-backward-theorem)
  (define-key coq-mode-map [f3] 'coq-theorem-forward)
)

(defvar coq-mode-syntax-table
  (let ((st (make-syntax-table)))
    (modify-syntax-entry ?\$ "." st)
    (modify-syntax-entry ?\/ "." st)
    (modify-syntax-entry ?\\ "." st)
    (modify-syntax-entry ?+  "." st)
    (modify-syntax-entry ?-  "." st)
    (modify-syntax-entry ?=  "." st)
    (modify-syntax-entry ?%  "." st)
    (modify-syntax-entry ?<  "." st)
    (modify-syntax-entry ?>  "." st)
    (modify-syntax-entry ?\& "." st)
    (modify-syntax-entry ?\| "." st)
    ;; quote is part of words
    (modify-syntax-entry ?\' "w" st)
    ;; underline is part of symbols
    (modify-syntax-entry ?_  "_" st)
    ;; * is second character of comment start,
    ;; and first character of comment end
    (modify-syntax-entry ?\* ". 23n" st)
    ;; ( is first character of comment start
    (modify-syntax-entry ?\( "()1" st)
    ;; ) is last character of comment end
    (modify-syntax-entry ?\) ")(4" st)
    st)
  "Syntax table for `coq-mode'.")

(defvar coq-mode-indentation 2
  "Indentation for each extra tab in Coq mode.")

(defun coq-mode-variables ()
  (set-syntax-table coq-mode-syntax-table)
  (make-local-variable 'paragraph-start)
  (setq paragraph-start (concat "^$\\|" page-delimiter))
  (make-local-variable 'paragraph-separate)
  (setq paragraph-separate paragraph-start)
  (make-local-variable 'paragraph-ignore-fill-prefix)
  (setq paragraph-ignore-fill-prefix t)
  (make-local-variable 'require-final-newline)
  (setq require-final-newline t)
  (make-local-variable 'comment-start)
  (setq comment-start "(* ")
  (make-local-variable 'comment-end)
  (setq comment-end " *)")
  (make-local-variable 'comment-column)
  (setq comment-column 40)
  (make-local-variable 'comment-start-skip)
  (setq comment-start-skip "(\\*+ *")
  (make-local-variable 'parse-sexp-ignore-comments)
  (setq parse-sexp-ignore-comments nil)
  (make-local-variable 'indent-line-function)
  (setq indent-line-function 'coq-indent-command))

;;;###autoload
(defun coq-mode ()
  "Major mode for editing Coq code.
Tab at the beginning of a line indents this line like the line above.
Extra tabs increase the indentation level.
\\{coq-mode-map}
The variable coq-mode-indentation indicates how many spaces are
inserted for each indentation level."
  (interactive)
  (kill-all-local-variables)
  (setq major-mode 'coq-mode)
  (setq mode-name "coq")
  (use-local-map coq-mode-map)
  (coq-mode-variables)
  (set (make-local-variable 'font-lock-defaults)
       '(coq-font-lock-keywords))
  (set (make-local-variable 'imenu-generic-expression)
       coq-imenu-generic-expression)
  (setq imenu-case-fold-search nil)
  (imenu-add-menubar-index)
  (run-hooks 'coq-mode-hook))

(defun coq-forward-vernac ()
  "Move forward one Coq vernac phrase.  Return the number of travelled
chars, either positive or 0."
  (interactive)
  (let ((pos (point)))
    (while (and (re-search-forward "(\\*\\|\\.\\(\\S_\\)" nil t)
		(goto-char (match-beginning 0))
		(not (when (match-beginning 1)
		       (goto-char (match-beginning 1))))
		(forward-comment 1)))
    (- (point) pos)))

(defun coq-backward-vernac ()
  "Move backward one Coq vernac phrase.  Return the number of
travelled chars, either negative or 0."
  (interactive)
  (let ((pos (point)))
    ;; Skip comments.
    (while (forward-comment -1))
    ;; Skip a "."
    (skip-chars-backward ".")
    ;; Search "." (skip comments).
    (while (and (re-search-backward "\\(\\*)\\)\\|\\." nil t)
		(goto-char (match-end 0))
		(match-end 1)
		(forward-comment -1)))
    (- (point) pos)))

(defvar coq-keywords-theorem
  '(
    "Definition"
    "Fact"
    "Lemma"
    "Local"
    "Remark"
    "Theorem"
   ))

(defvar coq-keywords-declaration 
  '(
    "Axiom"
    "Cofixpoint"
    "Fixpoint"
    "Hypothesis"
    "Inductive"
    "Mutual Inductive"
    "Parameter"
    "Parameters"
    "Tactic Definition"
    "Variable" 
    "Variables"
   ))

(defun coq-search-theorem-backward ()
  (interactive)
  (save-excursion
    (let ((pos nil))
      (while (and (not pos) (< (coq-backward-vernac)))
	(setq pos 
	      (and (re-search-forward
		    (concat "\=" (regexp-opt coq-keywords-theorem t))
		    nil t)
		   (match-beginning 0)))))))

(defun coq-backward-theorem ()
  (interactive)
  (let ((pos (coq-search-theorem-backward)))
    (if pos (goto-char pos))))

;; (defun coq-calculate-indent (&optional parse-start)
;;   "Return appropriate indentation for current line as Coq code.
;; In usual case returns an integer: the column to indent to.
;; If the value is nil, that means don't change the indentation
;; because the line starts inside a string.
;; 
;; The value can also be a list of the form (COLUMN CONTAINING-SEXP-START).
;; This means that following lines at the same level of indentation
;; should not necessarily be indented the same as this line.
;; Then COLUMN is the column to indent to, and CONTAINING-SEXP-START
;; is the buffer position of the start of the containing expression."
;;   (save-excursion
;;     (beginning-of-line)
;;     (let ((indent-point (point))
;;           state paren-depth
;;           ;; setting this to a number inhibits calling hook
;;           (desired-indent nil)
;;           (retry t)
;;           calculate-lisp-indent-last-sexp containing-sexp)
;;       (if parse-start
;;           (goto-char parse-start)
;;           (beginning-of-defun))
;;       ;; Find outermost containing sexp
;;       (while (< (point) indent-point)
;;         (setq state (parse-partial-sexp (point) indent-point 0)))
;;       ;; Find innermost containing sexp
;;       (while (and retry
;; 		  state
;;                   (> (setq paren-depth (elt state 0)) 0))
;;         (setq retry nil)
;;         (setq calculate-lisp-indent-last-sexp (elt state 2))
;;         (setq containing-sexp (elt state 1))
;;         ;; Position following last unclosed open.
;;         (goto-char (1+ containing-sexp))
;;         ;; Is there a complete sexp since then?
;;         (if (and calculate-lisp-indent-last-sexp
;; 		 (> calculate-lisp-indent-last-sexp (point)))
;;             ;; Yes, but is there a containing sexp after that?
;;             (let ((peek (parse-partial-sexp calculate-lisp-indent-last-sexp
;; 					    indent-point 0)))
;;               (if (setq retry (car (cdr peek))) (setq state peek)))))
;;       (if retry
;;           nil
;;         ;; Innermost containing sexp found
;;         (goto-char (1+ containing-sexp))
;;         (if (not calculate-lisp-indent-last-sexp)
;; 	    ;; indent-point immediately follows open paren.
;; 	    ;; Don't call hook.
;;             (setq desired-indent (current-column))
;; 	  ;; Find the start of first element of containing sexp.
;; 	  (parse-partial-sexp (point) calculate-lisp-indent-last-sexp 0 t)
;; 	  (cond ((looking-at "\\s(")
;; 		 ;; First element of containing sexp is a list.
;; 		 ;; Indent under that list.
;; 		 )
;; 		((> (save-excursion (forward-line 1) (point))
;; 		    calculate-lisp-indent-last-sexp)
;; 		 ;; This is the first line to start within the containing sexp.
;; 		 ;; It's almost certainly a function call.
;; 		 (if (= (point) calculate-lisp-indent-last-sexp)
;; 		     ;; Containing sexp has nothing before this line
;; 		     ;; except the first element.  Indent under that element.
;; 		     nil
;; 		   ;; Skip the first element, find start of second (the first
;; 		   ;; argument of the function call) and indent under.
;; 		   (progn (forward-sexp 1)
;; 			  (parse-partial-sexp (point)
;; 					      calculate-lisp-indent-last-sexp
;; 					      0 t)))
;; 		 (backward-prefix-chars))
;; 		(t
;; 		 ;; Indent beneath first sexp on same line as
;; 		 ;; `calculate-lisp-indent-last-sexp'.  Again, it's
;; 		 ;; almost certainly a function call.
;; 		 (goto-char calculate-lisp-indent-last-sexp)
;; 		 (beginning-of-line)
;; 		 (parse-partial-sexp (point) calculate-lisp-indent-last-sexp
;; 				     0 t)
;; 		 (backward-prefix-chars)))))
;;       ;; Point is at the point to indent under unless we are inside a string.
;;       ;; Call indentation hook except when overridden by lisp-indent-offset
;;       ;; or if the desired indentation has already been computed.
;;       (let ((normal-indent (current-column)))
;;         (cond ((elt state 3)
;;                ;; Inside a string, don't change indentation.
;; 	       nil)
;;               ((and (integerp lisp-indent-offset) containing-sexp)
;;                ;; Indent by constant offset
;;                (goto-char containing-sexp)
;;                (+ (current-column) lisp-indent-offset))
;;               (desired-indent)
;;               ((and (boundp 'lisp-indent-function)
;;                     lisp-indent-function
;;                     (not retry))
;;                (or (funcall lisp-indent-function indent-point state)
;;                    normal-indent))
;;               (t
;;                normal-indent))))))

;;; Indentation stuff

(defun coq-in-indentation ()
  "Tests whether all characters between beginning of line and point
are blanks."
  (save-excursion
    (skip-chars-backward " \t")
    (bolp)))

(defun coq-indent-command ()
  "Indent the current line in Coq mode.
When the point is at the beginning of an empty line, indent this line like
the line above.
When the point is at the beginning of an indented line
\(i.e. all characters between beginning of line and point are blanks\),
increase the indentation by one level.
The indentation size is given by the variable coq-mode-indentation.
In all other cases, insert a tabulation (using insert-tab)."
  (interactive)
  (let* ((begline
          (save-excursion
            (beginning-of-line)
            (point)))
         (current-offset
          (- (point) begline))
         (previous-indentation
          (save-excursion
            (if (eq (forward-line -1) 0) (current-indentation) 0))))
    (cond ((and (bolp)
                (looking-at "[ \t]*$")
                (> previous-indentation 0))
           (indent-to previous-indentation))
          ((coq-in-indentation)
           (indent-to (+ current-offset coq-mode-indentation)))
          (t
           (insert-tab)))))

(defun coq-unindent-command ()
  "Decrease indentation by one level in Coq mode.
Works only if the point is at the beginning of an indented line
\(i.e. all characters between beginning of line and point are blanks\).
Does nothing otherwise."
  (interactive)
  (let* ((begline
          (save-excursion
            (beginning-of-line)
            (point)))
         (current-offset
          (- (point) begline)))
    (if (and (>= current-offset coq-mode-indentation)
             (coq-in-indentation))
        (backward-delete-char-untabify coq-mode-indentation))))

;(defvar coq-font-lock-keywords
(setq coq-font-lock-keywords
  '(("\\<\\(Axiom\\|Parameter\\|\\Fixpoint\\|Cofixpoint\\|Inductive\\|Definition\\|Hypothesis\\|Local\\|Record\\|Variables?\\|Lemma\\|Remark\\|Fact\\|Theorem\\)\\s-+\\(\\(\\sw\\|\\s_\\)+\\)"
     2 font-lock-function-name-face)
    ;(",\\s-*\\(\\(\\sw\\|\\s_\\)+\\)\\s-*" 1 font-lock-function-name-face)
    ("\\(Section\\|End\\)\\s-+\\(\\(\\sw\\|\\s_\\)+\\)\\s-*."
     2 font-lock-function-name-face)
    ("Require\\(\\s-+Export\\)?\\s-+\\(\\(\\sw\\|\\s_\\)+\\)\\s-*."
     2 font-lock-function-name-face)
    ("\\<\\(Axiom\\|Parameter\\|Fixpoint\\|Cofixpoint\\|Inductive\\|Theorem\\|Defined\\|Save\\|Tactic\\|Definition\\|Fact\\|Hypothesis\\|Local\\|Require\\|Export\\|Record\\|\\Variables?\\|Section\\|End\\|Lemma\\|Remark\\|Proof\\|Qed\\|Hints?\\|Resolve\\)\\>" . font-lock-keyword-face)
    ("\\<\\(Type\\|Set\\|Prop\\)\\>" . font-lock-builtin-face)))
;  "Keyword highlighting specification for `coq-mode'.")

(defvar coq-imenu-generic-expression
  '(("Definitions"
     "\\<\\(Inductive\\|Definition\\)\\s-+\\(\\(\\sw\\|\\s_\\)+\\)\\s-*:" 2)
    ("Axioms"
     "\\<\\(Axioms\\|Parameter\\)\\s-+\\(\\(\\sw\\|\\s_\\)+\\)\\s-*:" 2)
    ("Fixpoints"
     "\\<\\(Cof\\|F\\)ixpoint\\s-+\\(\\(\\sw\\|\\s_\\)+\\)\\s-*:" 2)
    ("Theorems"
     "\\<Theorem\\s-+\\(\\(\\sw\\|\\s_\\)+\\)\\s-*:" 1)
    ("Lemmas"
     "\\<Lemma\\s-+\\(\\(\\sw\\|\\s_\\)+\\)\\s-*:" 1)
    ("Sections"
     "\\<Section\\s-+\\(\\(\\sw\\|\\s_\\)+\\)\\s-*." 1))
  "The regex pattern to use for imenu in `coq-mode'.")

;;; coq.el ends here

(provide 'coq)
