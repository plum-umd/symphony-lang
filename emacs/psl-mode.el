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
                           "def" "λ" "fun" "Λ" "abs" "∀" "forall" 
                           "in" "if" "then" "else" "case"
                           "mpc" "reveal" "share"))
             (x-types '("yao" "gmw" "bgw"
                        "nshare" "yshare" "gshare" "sshare"
                        "ncir" "bcir" "acir" "ccir" "ucir"
                        "ssec" "isec"
                        "☆" "type" 
                        "ℙ" "prin"
                        "𝟘" "empty"
                        "𝟙" "unit"
                        "𝔹" "bool"
                        "𝕊" "string"
                        "ℕ" "nat"
                        "ℤ" "int" 
                        "𝔽" "flt"
                        "list"
                        "read"
                        "inp" "rev" "par"
                        "true"
                        "false" "𝟙" "unit" "•" "()" "𝟘" "empty" "∷" "::"
                        "bcir" "sec" "par"))
             (x-events '("(" ")" "{" "}" "[" "]" "⟨" "⟩" "<" ">" 
                         "." "," ":" ";"
                         "→" "->" 
                         "⇒" "=>"
                         "="
                         "~"
                         "_"
                         "⁇" "??"
                         "@"
                         "⊆" "c="))
             (x-functions '("•" "()"
                            "[]"
                            "∷" "::"
                            "⟨⟩" "<>"
                            "+" "-" 
                            "×" "*" 
                            "/" 
                            "≡" "==" 
                            "≤" "<=" 
                            "⋖" "<<"
                            "^"
                            "?" 
                            "◇"))
             (x-constants '("true" "false"))

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
