;;;###autoload
(add-to-list 'auto-mode-alist '("\\.psl\\'" . psl-mode))


(setq psl-font-lock-keywords
      (let* (
	     (x-keywords '("primitive"
			   "principal"
			   "def"
			   "sec"
			   "tdef"
			   "λ" "fun"
			   "Λ"
			   "abs"
			   "∀" "forall"
			   "let"
			   "in"
			   "if"
			   "mux"
			   "then"
			   "else"
			   "case"
			   "reveal"
			   "share"
			   "protocol"
			   "trace"
			   "par"
			   "solo"
			   "as"
			   "fold"
			   "on"
			   "send"
			   "ref"
			   "do"
			   "array"
			   "from"
			   "to"
			   "read"
			   "write"
			   "proc"
			   "return"
			   "loop"
			   "when"
			   "import"
			   "with"
			   "nizk-witness"
			   "nizk-commit"
			   "virtual" "party"
			   "sign" "unsign" "is-signed"
			   ))
	     (x-types '("yao" "gmw" "bgw" "bgv" "spdz"
			"ssec" "isec" "bundle" "auto"
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
			"rand" "rand-range"
			"inp"
			"rev"
			"mpc"
			"all"
			"size"
			"nizk-test"
			"nizk-verify"
			"⊤"
			))
	     (x-constants '("•"
			    "()"
			    "[]"
			    "∷" "::"
			    "⟪⟫" "<<>>"
			    "{}"
			    "+"
			    "-"
			    "×" "*"
			    "%"
			    "/"
			    "≡" "=="
			    "≤" "<="
			    "≥" ">="
			    "<"
			    ">"
			    "^"
			    "?"
			    "◇"
			    "><"
			    "∨" "||"
			    "∧" "&&"
			    "⧺" "++"
			    "∪" "\/"
			    "→" "->"
			    "←" "<-"
			    ))
	     (x-events '("(" ")"
			 "{" "}"
			 "[" "]"
			 "⟪" "⟫"
			 "<<" ">>"
			 "."
			 ","
			 ":"
			 ";"
			 "⇒" "=>"
			 "="
			 "⁇" "??"
			 "@"
			 "⊆" "c="
			 "#"
			 "|"
			 "!"
			 "≔" ":="
			 "⊥" "_|_"
			 ))
	     (x-functions '("true"
			    "false"
			    "L"
			    "R"
			    ))

            (x-keywords-regexp (regexp-opt x-keywords 'words))
            (x-types-regexp (regexp-opt x-types 'words))
            (x-constants-regexp (regexp-opt x-constants))
            (x-events-regexp (regexp-opt x-events))
            (x-functions-regexp (regexp-opt x-functions 'words)))

        `(
          (,x-types-regexp . font-lock-type-face)
          (,x-constants-regexp . font-lock-constant-face)
          (,x-events-regexp . font-lock-builtin-face)
          (,x-functions-regexp . font-lock-function-name-face)
          (,x-keywords-regexp . font-lock-keyword-face)
          )))

;;;###autoload
(define-derived-mode psl-mode haskell-mode "psl mode"
  "Major mode for PSL"

  (setq font-lock-defaults '((psl-font-lock-keywords))))

(provide 'psl-mode)
