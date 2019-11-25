if exists("b:current_syntax")
  finish
endif

let b:current_syntax = "pantheon"

set iskeyword+=-

syn match pantheonKeyword "\v<def>"
syn match pantheonKeyword "\v<principal>"
syn match pantheonKeyword "\v<let>"
syn match pantheonKeyword "\v<in>"
syn match pantheonKeyword "\v<λ>"
syn match pantheonKeyword "\v<fun>"
syn match pantheonKeyword "\v<MPC>"
syn match pantheonKeyword "\v<mpc>"
syn match pantheonKeyword "\v<reveal>"

syn match pantheonPrimitive "\v<sec>"
syn match pantheonPrimitive "\v<ssec>"
syn match pantheonPrimitive "\v<isec>"
syn match pantheonPrimitive "\v<psec>"
syn match pantheonPrimitive "\v<ncir>"
syn match pantheonPrimitive "\v<bcir>"
syn match pantheonPrimitive "\v<acir>"
syn match pantheonPrimitive "\v<ccir>"
syn match pantheonPrimitive "\v<ucir>"
syn match pantheonPrimitive "\v<ashare>"
syn match pantheonPrimitive "\v<sshare>"
syn match pantheonPrimitive "\v<yshare>"
syn match pantheonPrimitive "\v<nshare>"
syn match pantheonPrimitive "\v<yao>"
syn match pantheonPrimitive "\v<gmw>"
syn match pantheonPrimitive "\v<bgw>"
syn match pantheonPrimitive "\v<read>"

syn match pantheonPrimitive "\v𝔹"
syn match pantheonPrimitive "\vℕ"
syn match pantheonPrimitive "\vℤ"
syn match pantheonPrimitive "\vℙ"
syn match pantheonPrimitive "\v𝟙"

syn match pantheonNoMatch "\v\w𝔹|𝔹\w"
syn match pantheonNoMatch "\v\wℕ|ℕ\w"
syn match pantheonNoMatch "\v\wℤ|ℤ\w"
syn match pantheonNoMatch "\v\wℙ|ℙ\w"
syn match pantheonNoMatch "\v\w𝟙|𝟙\w"

syn match pantheonPrimitive "\vℤ64"
syn match pantheonNoMatch "\v\wℤ64|ℤ64\w"

syn match pantheonPunctuation "\v\("
syn match pantheonPunctuation "\v\)"
syn match pantheonPunctuation "\v\{"
syn match pantheonPunctuation "\v\}"
syn match pantheonPunctuation "\v\["
syn match pantheonPunctuation "\v\]"
syn match pantheonPunctuation "\v⟨"
syn match pantheonPunctuation "\v⟩"
syn match pantheonPunctuation "\v,"
syn match pantheonPunctuation "\v\."
syn match pantheonPunctuation "\v:"
syn match pantheonPunctuation "\v;"
syn match pantheonPunctuation "\v\="
syn match pantheonPunctuation "\v→"
syn match pantheonPunctuation "\v\<-"
syn match pantheonPunctuation "\v←"
syn match pantheonPunctuation "\v-\>"
syn match pantheonPunctuation "\v⇒"
syn match pantheonPunctuation "\v\=\>"
syn match pantheonPunctuation "\v\~"
syn match pantheonPunctuation "\v⪫"
syn match pantheonPunctuation "\v\@"

"syn match pantheonPunctuation "\v/"
"syn match pantheonPunctuation "\v;"
"syn match pantheonPunctuation "\v\="
"syn match pantheonPunctuation "\v\>"
"syn match pantheonPunctuation "\v\>-\>"
"syn match pantheonPunctuation "\v←"
"syn match pantheonPunctuation "\v→⋆"
"syn match pantheonPunctuation "\v↣"
"syn match pantheonPunctuation "\v\$"
"syn match pantheonPunctuation "\v⇉"
"syn match pantheonPunctuation "\v⌊"
"syn match pantheonPunctuation "\v⌋"
"syn match pantheonPunctuation "\v⌈"
"syn match pantheonPunctuation "\v⌉"
"syn match pantheonPunctuation "\v⪪"
"syn match pantheonPunctuation "\v⫫"
"syn match pantheonPunctuation "\v∀"
"syn match pantheonPunctuation "\v⇒"
"syn match pantheonPunctuation "\v⊆"
"syn match pantheonPunctuation "\v∈"
"syn match pantheonPunctuation "\v_"

syn match pantheonOperator "\v≤"
syn match pantheonOperator "\v\<\="
syn match pantheonOperator "\v\+"
syn match pantheonOperator "\v\-"
syn match pantheonOperator "\v•"

"syn match pantheonOperator "\v\-"
"syn match pantheonOperator "\v\<"
"syn match pantheonOperator "\v≡"
"syn match pantheonOperator "\v\=\="
"syn match pantheonOperator "\v×"
"syn match pantheonOperator "\v∧"
"syn match pantheonOperator "\v∨"
"syn match pantheonOperator "\v\*"
"syn match pantheonOperator "\v◇"
"syn match pantheonOperator "\v\?"
"syn match pantheonOperator "\v\(\)"
"syn match pantheonOperator "\v\[\]"
"syn match pantheonOperator "\v∷"
"syn match pantheonOperator "\v\:\:"

syn match pantheonNoMatch "\v\S\-|\-\S"

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
