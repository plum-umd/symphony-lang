;; An emacs mode for editing Psl code

(defvar psl-mode-syntax-table nil "Syntax table for `psl-mode'.")

(setq psl-mode-syntax-table
      (let ((synTable (make-syntax-table)))
        (modify-syntax-entry ?- ". 12b" synTable)
        (modify-syntax-entry ?\n "> b" synTable)
        synTable))

(setq psl-font-lock-keywords
      (let* (
             ;; define several category of keywords
             (x-keywords '("primitive" "principal" "trust" "security"
                           "def" "λ" "fun" "Λ" "abs" "let" "in" "if"
                           "then" "else" "circuit" "mpc" "do" "case"
                           "rλ" "rfun"))
             (x-types '("yao" "bgw" "gmw" "none" "☆" "type" "ℙ" "prin"
                        "ℤ" "int" "𝔹" "bool" "MPC" "CIR" "list" "true"
                        "false" "𝟙" "unit" "•" "()" "𝟘" "empty" "∷" "::"))
             (x-events '("(" ")" "{" "}" "[" "]" "<" ">" "⟨" "⟩" " " ":"
                         ";" "→" "->" "←" "<-" "↣" ">->" "⪫" "->-" "⫫"
                         "_||_" "=" "~" "_"))
             (x-functions '("+" "-" "×" "*" "/" "≡" "==" "≤" "<=" "<" "^"))
             (x-constants '())

            ;; generate regex string for each category of keywords
            (x-keywords-regexp (regexp-opt x-keywords 'words))
            (x-types-regexp (regexp-opt x-types 'words))
            (x-constants-regexp (regexp-opt x-constants 'words))
            (x-events-regexp
             (mapconcat 'identity (mapcar (function (lambda (x) (concat x "\\|"))) x-events) ""))
            (x-functions-regexp (regexp-opt x-functions 'words)))

        `(
          (,x-types-regexp . font-lock-type-face)
          (,x-constants-regexp . font-lock-constant-face)
          (,x-events-regexp . font-lock-builtin-face)
          (,x-functions-regexp . font-lock-function-name-face)
          (,x-keywords-regexp . font-lock-keyword-face)
          )))

(define-derived-mode psl-mode prog-mode "PSL mode"
  "Major mode for editing PSL code"
  (setq font-lock-defaults '((psl-font-lock-keywords))))

(provide 'psl-mode)
