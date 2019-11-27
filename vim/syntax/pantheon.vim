if exists("b:current_syntax")
  finish
endif

let b:current_syntax = "pantheon"

set iskeyword+=-

syn match pantheonKeyword "\v<primitive>"
syn match pantheonKeyword "\v<principal>"
syn match pantheonKeyword "\v<trust>"
syn match pantheonKeyword "\v<security>"
syn match pantheonKeyword "\v<def>"
syn match pantheonKeyword "\v<λ>"
syn match pantheonKeyword "\v<fun>"
syn match pantheonKeyword "\v<Λ>"
syn match pantheonKeyword "\v<abs>"
syn match pantheonKeyword "\v<∀>"
syn match pantheonKeyword "\v<forall>"
syn match pantheonKeyword "\v<let>"
syn match pantheonKeyword "\v<in>"
syn match pantheonKeyword "\v<if>"
syn match pantheonKeyword "\v<then>"
syn match pantheonKeyword "\v<else>"
syn match pantheonKeyword "\v<case>"
syn match pantheonKeyword "\v<mpc>"
syn match pantheonKeyword "\v<reveal>"

syn match pantheonPrimitive "\v<yao>"
syn match pantheonPrimitive "\v<gmw>"
syn match pantheonPrimitive "\v<bgw>"
syn match pantheonPrimitive "\v<nshare>"
syn match pantheonPrimitive "\v<yshare>"
syn match pantheonPrimitive "\v<gshare>"
syn match pantheonPrimitive "\v<sshare>"
syn match pantheonPrimitive "\v<ncir>"
syn match pantheonPrimitive "\v<bcir>"
syn match pantheonPrimitive "\v<acir>"
syn match pantheonPrimitive "\v<ccir>"
syn match pantheonPrimitive "\v<ucir>"
syn match pantheonPrimitive "\v<ssec>"
syn match pantheonPrimitive "\v<isec>"
syn match pantheonPrimitive "\v<type>"
syn match pantheonPrimitive "\v<prin>"
syn match pantheonPrimitive "\v<empty>"
syn match pantheonPrimitive "\v<unit>"
syn match pantheonPrimitive "\v<bool>"
syn match pantheonPrimitive "\v<string>"
syn match pantheonPrimitive "\v<nat>"
syn match pantheonPrimitive "\v<int>"
syn match pantheonPrimitive "\v<flt>"
syn match pantheonPrimitive "\v<list>"
syn match pantheonPrimitive "\v<read>"
syn match pantheonPrimitive "\v<inp>"
syn match pantheonPrimitive "\v<rev>"

syn match pantheonPrimitive "\v☆"
syn match pantheonPrimitive "\vℙ"
syn match pantheonPrimitive "\v𝟘"
syn match pantheonPrimitive "\v𝟙"
syn match pantheonPrimitive "\v𝔹"
syn match pantheonPrimitive "\v𝕊"
syn match pantheonPrimitive "\vℕ"
syn match pantheonPrimitive "\vℤ"
syn match pantheonPrimitive "\v𝔽"

syn match pantheonNoMatch "\v\w☆|☆\w"
syn match pantheonNoMatch "\v\wℙ|ℙ\w"
syn match pantheonNoMatch "\v\w𝟘|𝟘\w"
syn match pantheonNoMatch "\v\w𝟙|𝟙\w"
syn match pantheonNoMatch "\v\w𝔹|𝔹\w"
syn match pantheonNoMatch "\v\w𝕊|𝕊\w"
syn match pantheonNoMatch "\v\wℕ|ℕ\w"
syn match pantheonNoMatch "\v\wℤ|ℤ\w"
syn match pantheonNoMatch "\v\w𝔽|𝔽\w"

syn match pantheonPunctuation "\v\("
syn match pantheonPunctuation "\v\)"
syn match pantheonPunctuation "\v\{"
syn match pantheonPunctuation "\v\}"
syn match pantheonPunctuation "\v\["
syn match pantheonPunctuation "\v\]"
syn match pantheonPunctuation "\v⟨"
syn match pantheonPunctuation "\v⟩"
syn match pantheonPunctuation "\v\<"
syn match pantheonPunctuation "\v\>"
syn match pantheonPunctuation "\v\."
syn match pantheonPunctuation "\v,"
syn match pantheonPunctuation "\v:"
syn match pantheonPunctuation "\v;"
syn match pantheonPunctuation "\v→"
syn match pantheonPunctuation "\v-\>"
syn match pantheonPunctuation "\v⇒"
syn match pantheonPunctuation "\v\=\>"
syn match pantheonPunctuation "\v\="
syn match pantheonPunctuation "\v\~"
syn match pantheonPunctuation "\v_"
syn match pantheonPunctuation "\v⁇"
syn match pantheonPunctuation "\v\?\?"
syn match pantheonPunctuation "\v\@"
syn match pantheonPunctuation "\v⊆"
syn match pantheonPunctuation "\vc\="

syn match pantheonOperator "\v•"
syn match pantheonOperator "\v\(\)"
syn match pantheonOperator "\v\[\]"
syn match pantheonOperator "\v∷"
syn match pantheonOperator "\v\:\:"
syn match pantheonOperator "\v⟨⟩"
syn match pantheonOperator "\v\<\>"
syn match pantheonOperator "\v\+"
syn match pantheonOperator "\v\-"
syn match pantheonOperator "\v×"
syn match pantheonOperator "\v\*"
syn match pantheonOperator "\v\/"
syn match pantheonOperator "\v≡"
syn match pantheonOperator "\v\=\="
syn match pantheonOperator "\v≤"
syn match pantheonOperator "\v\<\="
syn match pantheonOperator "\v⋖"
syn match pantheonOperator "\v\<\<"
syn match pantheonOperator "\v\^"
syn match pantheonOperator "\v\?"
syn match pantheonOperator "\v◇"

syn match pantheonNoMatch "\v\S\-|\-\S"

syn match pantheonLiteral "\v<true>"
syn match pantheonLiteral "\v<false>"

syn match pantheonLiteral "\v-?\d+(\.\d+)?(e\d+)?"
syn match pantheonLiteral "\v\"([^\"\\]|([\\][\"]))*\""

syn match pantheonComment "\v--.*$"
syn region pantheonCommentML start="\v\{-" end="\v-\}" contains=pantheonCommentML

hi def link pantheonKeyword PantheonKeyword
hi def link pantheonPrimitive PantheonIdentifier
hi def link pantheonOperator PantheonOperator
hi def link pantheonPunctuation PantheonPunctuation
hi def link pantheonComment PantheonComment
hi def link pantheonCommentML PantheonComment

if &background ==# 'light'

highlight PantheonKeyword     term=bold cterm=bold     ctermfg=darkYellow
highlight PantheonPrimitive                            ctermfg=darkBlue
highlight PantheonOperator                             ctermfg=darkGreen
highlight PantheonPunctuation                          ctermfg=darkGray
highlight PantheonLiteral                              ctermfg=darkRed
highlight PantheonComment     term=italic cterm=italic ctermfg=gray

else " background ==# 'dark'

highlight PantheonKeyword     term=bold cterm=bold     ctermfg=yellow
highlight PantheonPrimitive                            ctermfg=lightBlue
highlight PantheonOperator                             ctermfg=lightGreen
highlight PantheonPunctuation                          ctermfg=gray
highlight PantheonLiteral                              ctermfg=lightRed
highlight PantheonComment     term=italic cterm=italic ctermfg=darkGray

endif
