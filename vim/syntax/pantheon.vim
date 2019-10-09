if exists("b:current_syntax")
  finish
endif

let b:current_syntax = "pantheon"

syn match pantheonKeyword "\v<CIR>"
syn match pantheonKeyword "\v<MPC>"
syn match pantheonKeyword "\v<circuit>"
syn match pantheonKeyword "\v<def>"
syn match pantheonKeyword "\v<do>"
syn match pantheonKeyword "\v<else>"
syn match pantheonKeyword "\v<exe>"
syn match pantheonKeyword "\v<if>"
syn match pantheonKeyword "\v<in>"
syn match pantheonKeyword "\v<let>"
syn match pantheonKeyword "\v<mpc>"
syn match pantheonKeyword "\v<primitive>"
syn match pantheonKeyword "\v<principal>"
syn match pantheonKeyword "\v<return>"
syn match pantheonKeyword "\v<sec>"
syn match pantheonKeyword "\v<security>"
syn match pantheonKeyword "\v<then>"
syn match pantheonKeyword "\v<trust>"
syn match pantheonKeyword "\v<wire>"
syn match pantheonKeyword "\v<Λ>"
syn match pantheonKeyword "\v<λ>"
syn match pantheonKeyword "\v<λc>"
syn match pantheonKeyword "\v<λmpc>"

syn match pantheonPrimitive "\v<P>"
syn match pantheonPrimitive "\v<R>"
syn match pantheonPrimitive "\v<S>"
syn match pantheonPrimitive "\v<bgw>"
syn match pantheonPrimitive "\v<gmw>"
syn match pantheonPrimitive "\v<yao>"
syn match pantheonPrimitive "\v<none>"

syn match pantheonPrimitive "\vℤ"
syn match pantheonPrimitive "\v○"
syn match pantheonPrimitive "\v𝔹"

syn match pantheonNoMatch "\v\w𝔹|𝔹\w"
syn match pantheonNoMatch "\v\wℤ|ℤ\w"
syn match pantheonNoMatch "\v\w○|○\w"


syn match pantheonOperator "\v\-"
syn match pantheonOperator "\v\<"
syn match pantheonOperator "\v\=\="
syn match pantheonOperator "\v×"
syn match pantheonOperator "\v◇"

syn match pantheonPunctuation "\v,"
syn match pantheonPunctuation "\v-\>"
syn match pantheonPunctuation "\v/"
syn match pantheonPunctuation "\v:"
syn match pantheonPunctuation "\v;"
syn match pantheonPunctuation "\v\("
syn match pantheonPunctuation "\v\)"
syn match pantheonPunctuation "\v\."
syn match pantheonPunctuation "\v\="
syn match pantheonPunctuation "\v\>"
syn match pantheonPunctuation "\v\>-\>"
syn match pantheonPunctuation "\v\["
syn match pantheonPunctuation "\v\]"
syn match pantheonPunctuation "\v\{"
syn match pantheonPunctuation "\v\|"
syn match pantheonPunctuation "\v\}"
syn match pantheonPunctuation "\v\~"
syn match pantheonPunctuation "\v←"
syn match pantheonPunctuation "\v→"
syn match pantheonPunctuation "\v→⋆"
syn match pantheonPunctuation "\v↣"
syn match pantheonPunctuation "\v⇉"
syn match pantheonPunctuation "\v⌊"
syn match pantheonPunctuation "\v⌋"
syn match pantheonPunctuation "\v⪪"
syn match pantheonPunctuation "\v⪫"
syn match pantheonPunctuation "\v⫫"

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
highlight PantheonComment     term=italic cterm=italic ctermfg=gray

else " background ==# 'dark'

highlight PantheonKeyword     term=bold cterm=bold     ctermfg=yellow
highlight PantheonPrimitive                            ctermfg=lightBlue
highlight PantheonOperator                             ctermfg=lightGreen
highlight PantheonPunctuation                          ctermfg=gray
highlight PantheonComment     term=italic cterm=italic ctermfg=darkGray

endif
