if exists("b:current_syntax")
  finish
endif

let b:current_syntax = "pantheonSecurity"

set iskeyword+=-

syn match pantheonPunctuation "\v\{"
syn match pantheonPunctuation "\v\}"
syn match pantheonPunctuation "\v\["
syn match pantheonPunctuation "\v\]"
syn match pantheonPunctuation "\v\-"
syn match pantheonPunctuation "\v\-\>"
syn match pantheonPunctuation "\v:"
syn match pantheonPunctuation "\v;"
syn match pantheonPunctuation "\v,"

syn match pantheonOperator "\v\<\="

syn match pantheonNoMatch "\v(\w|_)+(\-|\w|_)*"
syn match pantheonNoMatch "\v(\-|\w|_)*(\w|_)+"

syn match pantheonLiteral "\v<true>"
syn match pantheonLiteral "\v<false>"
syn match pantheonLiteral "\v<none>"

syn match pantheonLiteral "\v-?\d+(\.\d+)?(e\d+)?"
syn match pantheonLiteral "\v\"([^\"\\]|([\\][\"]))*\""

syn match pantheonKeyword "\v<security>"
syn match pantheonKeyword "\v<connected>"

syn match pantheonPrimitive "\v<all>"
syn match pantheonPrimitive "\v<nodes>"
syn match pantheonPrimitive "\v<edges>"
syn match pantheonPrimitive "\v<semi-honest>"
syn match pantheonPrimitive "\v<semi-malicious>"
syn match pantheonPrimitive "\v<covert>"
syn match pantheonPrimitive "\v<malicious>"
syn match pantheonPrimitive "\v<corruptible>"
syn match pantheonPrimitive "\v<location>"
syn match pantheonPrimitive "\v<ok-reveals>"
syn match pantheonPrimitive "\v<reveals>"
syn match pantheonPrimitive "\v<no-reveals>"
syn match pantheonPrimitive "\v<encryption>"
syn match pantheonPrimitive "\v<full>"
syn match pantheonPrimitive "\v<link>"
syn match pantheonPrimitive "\v<broadcast>"
syn match pantheonPrimitive "\v<trusted-setup>"
syn match pantheonPrimitive "\v<no-trusted-setup>"
syn match pantheonPrimitive "\v<pki>"
syn match pantheonPrimitive "\v<no-pki>"
syn match pantheonPrimitive "\v<crand>"

syn match pantheonOperator "\v\/"

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

