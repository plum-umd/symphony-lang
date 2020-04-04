if exists("b:current_syntax")
  finish
endif

let b:current_syntax = "pantheon"

set iskeyword+=-

syn match pantheonPunctuation "\v\("
syn match pantheonPunctuation "\v\)"
syn match pantheonPunctuation "\v\{"
syn match pantheonPunctuation "\v\}"
syn match pantheonPunctuation "\v\["
syn match pantheonPunctuation "\v\]"
syn match pantheonPunctuation "\v⟪"
syn match pantheonPunctuation "\v⟫"
syn match pantheonPunctuation "\v\<\<"
syn match pantheonPunctuation "\v\>\>"
syn match pantheonPunctuation "\v\."
syn match pantheonPunctuation "\v,"
syn match pantheonPunctuation "\v:"
syn match pantheonPunctuation "\v;"
syn match pantheonPunctuation "\v⇒"
syn match pantheonPunctuation "\v\=\>"
syn match pantheonPunctuation "\v\="
syn match pantheonPunctuation "\v⁇"
syn match pantheonPunctuation "\v\?\?"
syn match pantheonPunctuation "\v\@"
syn match pantheonPunctuation "\v⊆"
syn match pantheonPunctuation "\vc\="
syn match pantheonPunctuation "\v\#"
syn match pantheonPunctuation "\v\|"
syn match pantheonPunctuation "\v!"
syn match pantheonPunctuation "\v≔"
syn match pantheonPunctuation "\v:\="
syn match pantheonPunctuation "\v⊥"
syn match pantheonPunctuation "\v_\|_"

syn match pantheonOperator "\v•"
syn match pantheonOperator "\v\(\)"
syn match pantheonOperator "\v\[\]"
syn match pantheonOperator "\v∷"
syn match pantheonOperator "\v\:\:"
syn match pantheonOperator "\v⟪⟫"
syn match pantheonOperator "\v\<\<\>\>"
syn match pantheonOperator "\v\{\}"
syn match pantheonOperator "\v\+"
syn match pantheonOperator "\v\-"
syn match pantheonOperator "\v×"
syn match pantheonOperator "\v\%"
syn match pantheonOperator "\v\*"
syn match pantheonOperator "\v\/"
syn match pantheonOperator "\v≡"
syn match pantheonOperator "\v\=\="
syn match pantheonOperator "\v≤"
syn match pantheonOperator "\v\<\="
syn match pantheonOperator "\v\<"
syn match pantheonOperator "\v\>"
syn match pantheonOperator "\v\^"
syn match pantheonOperator "\v\?"
syn match pantheonOperator "\v◇"
syn match pantheonOperator "\v\>\<"
syn match pantheonOperator "\v\|\|"
syn match pantheonOperator "\v∨"
syn match pantheonOperator "\v\&\&"
syn match pantheonOperator "\v∧"
syn match pantheonOperator "\v⧺"
syn match pantheonOperator "\v\+\+"
syn match pantheonOperator "\v∪"
syn match pantheonOperator "\v\\/"

syn match pantheonPunctuation "\v→"
syn match pantheonPunctuation "\v←"
syn match pantheonPunctuation "\v\-\>"
syn match pantheonPunctuation "\v\<\-"

syn match pantheonNoMatch "\v(\w|_)+(\-|\w|_)*"
syn match pantheonNoMatch "\v(\-|\w|_)*(\w|_)+"

syn match pantheonLiteral "\v<true>"
syn match pantheonLiteral "\v<false>"

syn match pantheonLiteral "\v-?(\d|_)+(\.(\d|_)+)?(e(\d|_)+)?"
syn match pantheonLiteral "\v\d(\d|_)*n"
syn match pantheonLiteral "\v\"([^\"\\]|([\\][\"]))*\""

syn match pantheonPunctuation "\v_"

syn match pantheonOperator "\v<L>"
syn match pantheonOperator "\v<R>"

syn match pantheonKeyword "\v<primitive>"
syn match pantheonKeyword "\v<principal>"
syn match pantheonKeyword "\v<def>"
syn match pantheonKeyword "\v<tdef>"
syn match pantheonKeyword "\v<λ>"
syn match pantheonKeyword "\v<fun>"
syn match pantheonKeyword "\v<Λ>"
syn match pantheonKeyword "\v<abs>"
syn match pantheonKeyword "\v<forall>"
syn match pantheonKeyword "\v<let>"
syn match pantheonKeyword "\v<in>"
syn match pantheonKeyword "\v<if>"
syn match pantheonKeyword "\v<mux>"
syn match pantheonKeyword "\v<then>"
syn match pantheonKeyword "\v<else>"
syn match pantheonKeyword "\v<case>"
syn match pantheonKeyword "\v<reveal>"
syn match pantheonKeyword "\v<share>"
syn match pantheonKeyword "\v<protocol>"
syn match pantheonKeyword "\v<trace>"
syn match pantheonKeyword "\v<par>"
syn match pantheonKeyword "\v<solo>"
syn match pantheonKeyword "\v<as>"
syn match pantheonKeyword "\v<fold>"
syn match pantheonKeyword "\v<on>"
syn match pantheonKeyword "\v<send>"
syn match pantheonKeyword "\v<ref>"
syn match pantheonKeyword "\v<do>"
syn match pantheonKeyword "\v<array>"
syn match pantheonKeyword "\v<from>"
syn match pantheonKeyword "\v<to>"
syn match pantheonKeyword "\v<read>"
syn match pantheonKeyword "\v<write>"
syn match pantheonKeyword "\v<proc>"
syn match pantheonKeyword "\v<return>"
syn match pantheonKeyword "\v<loop>"
syn match pantheonKeyword "\v<when>"


syn match pantheonKeyword "\v∀"

syn match pantheonNoMatch "\v\w∀|∀\w"

syn match pantheonPrimitive "\v<yao>"
syn match pantheonPrimitive "\v<gmw>"
syn match pantheonPrimitive "\v<bgw>"
syn match pantheonPrimitive "\v<bgv>"
syn match pantheonPrimitive "\v<spdz>"
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
syn match pantheonPrimitive "\v<rand>"
syn match pantheonPrimitive "\v<rand-range>"
syn match pantheonPrimitive "\v<inp>"
syn match pantheonPrimitive "\v<rev>"
" syn match pantheonPrimitive "\v<par>"
" syn match pantheonPrimitive "\v<sec>"
syn match pantheonPrimitive "\v<mpc>"
syn match pantheonPrimitive "\v<all>"
syn match pantheonPrimitive "\v<size>"

syn match pantheonPrimitive "\v☆"
syn match pantheonPrimitive "\vℙ"
syn match pantheonPrimitive "\v𝟘"
syn match pantheonPrimitive "\v𝟙"
syn match pantheonPrimitive "\v𝔹"
syn match pantheonPrimitive "\v𝕊"
syn match pantheonPrimitive "\vℕ"
syn match pantheonPrimitive "\vℤ"
syn match pantheonPrimitive "\v𝔽"
syn match pantheonPrimitive "\v⊤"

syn match pantheonNoMatch "\v\w☆|☆\w"
syn match pantheonNoMatch "\v\wℙ|ℙ\w"
syn match pantheonNoMatch "\v\w𝟘|𝟘\w"
syn match pantheonNoMatch "\v\w𝟙|𝟙\w"
syn match pantheonNoMatch "\v\w𝔹|𝔹\w"
syn match pantheonNoMatch "\v\w𝕊|𝕊\w"
syn match pantheonNoMatch "\v\wℕ|ℕ\w"
syn match pantheonNoMatch "\v\wℤ|ℤ\w"
syn match pantheonNoMatch "\v\w𝔽|𝔽\w"
syn match pantheonNoMatch "\v\w⊤|⊤\w"

syn match pantheonPrimitive "\vℙs"
syn match pantheonNoMatch "\v\wℙs|ℙs\w"

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
