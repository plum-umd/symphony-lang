<!DOCTYPE HTML PUBLIC "-//W3C//DTD HTML 4.01//EN" "http://www.w3.org/TR/html4/strict.dtd">
<html>
<head>
<meta http-equiv="content-type" content="text/html; charset=UTF-8">
<title>~/Projects/psl/examples/cmp-tutorial.psl.html</title>
<meta name="Generator" content="Vim/8.1">
<meta name="plugin-version" content="vim8.1_v1">
<meta name="syntax" content="pantheon">
<meta name="settings" content="use_css,pre_wrap,no_foldcolumn,expand_tabs,prevent_copy=">
<meta name="colorscheme" content="none">
<style type="text/css">
<!--
pre { white-space: pre-wrap; font-family: monospace; color: #000000; background-color: #ffffff; }
body { font-family: monospace; color: #000000; background-color: #ffffff; }
* { font-size: 1em; }
.pantheonKeyword { color: #af5f00; font-weight: bold; }
.pantheonComment { color: #a8a8a8; font-style: italic; }
.pantheonPunctuation { color: #6c6c6c; }
.pantheonOperator { color: #008000; }
.pantheonLiteral { color: #c00000; }
.pantheonPrimitive { color: #0000c0; }
-->
</style>
</head>
<body>
<pre id='vimCodeElement'>
<span class="pantheonComment">{-</span>
<span class="pantheonComment">These lines declare that `A` and `B` are principles, and the type checker</span>
<span class="pantheonComment">(not yet implemented) will make sure that all principles mentioned in types</span>
<span class="pantheonComment">are (at least) well-scoped, and possibly also check some security relationships</span>
<span class="pantheonComment">as well, e.g., does A trust B, and to what extent.</span>

<span class="pantheonComment">These lines are ignored by the interpreter.</span>
<span class="pantheonComment">-}</span>
<span class="pantheonKeyword">principal</span> A
<span class="pantheonKeyword">principal</span> B

<span class="pantheonComment">{-</span>
<span class="pantheonComment">`cmp` takes a secret input from both `A` and `B` and builds a circuit which</span>
<span class="pantheonComment">compares them, returning a boolean.</span>

<span class="pantheonComment">The input variable `xy` has type `ℤ[64]{isec:A,B}`, which reads as “a 64-bit</span>
<span class="pantheonComment">integer as independent (i.e., not necessarily equal) secrets for each party `A`</span>
<span class="pantheonComment">and `B`.” To access `A`'s value, we write `xy.A`, and likewise for `B` and</span>
<span class="pantheonComment">`xy.B`. `xy.A` is a secret value, and can be embedded inside of a circuit with</span>
<span class="pantheonComment">`~xy.A`. All parties share this circuit, and `A`'s value inside `~xy` will be</span>
<span class="pantheonComment">provided as an input to the circuit when executed using a protocol (e.g. yao).</span>

<span class="pantheonComment">The access mode `isec` is distinguished from `ssec`, which reads as “shared</span>
<span class="pantheonComment">secret”, in that `ssec` values have the added invariant that all parties have a</span>
<span class="pantheonComment">local copy of the exact same value. E.g., when a result from mpc is revealed to</span>
<span class="pantheonComment">some subset of parties. `ssec` values can be used to construct new circuits,</span>
<span class="pantheonComment">whereas `isec` values cannot, or else we would have two parties evaluating</span>
<span class="pantheonComment">different circuits, which would be bad.</span>

<span class="pantheonComment">The return type `𝔹{ccir:A,B}` reads as “a circuit comprised of comparison</span>
<span class="pantheonComment">operations on numeric types with embedded secret inputs from `A` and `B`”.</span>
<span class="pantheonComment">The fact that a comparison operator is embedded in the circuit computation is</span>
<span class="pantheonComment">tracked coarsly at the type level. E.g., it may not be possible to execute a</span>
<span class="pantheonComment">`ccir` using bgw, and we want to throw a runtime error (and type error) if the</span>
<span class="pantheonComment">programmer tries to do it.</span>

<span class="pantheonComment">The first two steps of the function embed secret inputs from `A` and `B` into</span>
<span class="pantheonComment">single-node circuits—they are degenerate circuits with just the embedded secret</span>
<span class="pantheonComment">value. The type of these circuits is `ncir`, which says “no operations”. The</span>
<span class="pantheonComment">last step is a normal comparison operator which is overloaded syntactically to</span>
<span class="pantheonComment">operate over circuit values, giving a circuit result type `ccir` which tracks</span>
<span class="pantheonComment">the comparison operation.</span>
<span class="pantheonComment">-}</span>
<span class="pantheonKeyword">def</span> cmp <span class="pantheonPunctuation">:</span> <span class="pantheonPrimitive">ℤ</span><span class="pantheonPunctuation">[</span><span class="pantheonLiteral">64</span><span class="pantheonPunctuation">]{</span><span class="pantheonPrimitive">isec</span><span class="pantheonPunctuation">:</span>A<span class="pantheonPunctuation">,</span>B<span class="pantheonPunctuation">}</span> <span class="pantheonPunctuation">→</span> <span class="pantheonPrimitive">𝔹</span><span class="pantheonPunctuation">{</span><span class="pantheonPrimitive">ccir</span><span class="pantheonPunctuation">:</span>A<span class="pantheonPunctuation">,</span>B<span class="pantheonPunctuation">}</span>
<span class="pantheonKeyword">def</span> cmp <span class="pantheonPunctuation">=</span> <span class="pantheonKeyword">λ</span> xy <span class="pantheonPunctuation">→</span>
  <span class="pantheonKeyword">let</span> x <span class="pantheonPunctuation">:</span> <span class="pantheonPrimitive">ℤ</span><span class="pantheonPunctuation">[</span><span class="pantheonLiteral">64</span><span class="pantheonPunctuation">]{</span><span class="pantheonPrimitive">ncir</span><span class="pantheonPunctuation">:</span>A<span class="pantheonPunctuation">}</span>
  <span class="pantheonKeyword">let</span> x <span class="pantheonPunctuation">=</span> <span class="pantheonPunctuation">~</span>xy<span class="pantheonPunctuation">.</span>A
  <span class="pantheonKeyword">let</span> y <span class="pantheonPunctuation">:</span> <span class="pantheonPrimitive">ℤ</span><span class="pantheonPunctuation">[</span><span class="pantheonLiteral">64</span><span class="pantheonPunctuation">]{</span><span class="pantheonPrimitive">ncir</span><span class="pantheonPunctuation">:</span>B<span class="pantheonPunctuation">}</span>
  <span class="pantheonKeyword">let</span> y <span class="pantheonPunctuation">=</span> <span class="pantheonPunctuation">~</span>xy<span class="pantheonPunctuation">.</span>B
  <span class="pantheonKeyword">let</span> r <span class="pantheonPunctuation">:</span> <span class="pantheonPrimitive">𝔹</span><span class="pantheonPunctuation">{</span><span class="pantheonPrimitive">ccir</span><span class="pantheonPunctuation">:</span>B<span class="pantheonPunctuation">}</span>
  <span class="pantheonKeyword">let</span> r <span class="pantheonPunctuation">=</span> x <span class="pantheonOperator">≤</span> y
  <span class="pantheonKeyword">in</span> r

<span class="pantheonComment">{-</span>
<span class="pantheonComment">We have moved away from a monadic discipline for tracking effects, and are now</span>
<span class="pantheonComment">using a more traditional effect system, e.g., an effectful computation is a</span>
<span class="pantheonComment">function of a dummy argument `•` with an effect annotation over the arrow. The</span>
<span class="pantheonComment">effect in this function is `{inp:A,B;rev:}` which means “inputs are read from</span>
<span class="pantheonComment">parties `A` and `B`, but nothing is revealed to any part”. The thinking for now</span>
<span class="pantheonComment">is that it may be advantageous to track security-critical events in effect</span>
<span class="pantheonComment">types, at the very least for auditing. If I am using a library function or some</span>
<span class="pantheonComment">old code, what I really want to know from a security point of view is whether</span>
<span class="pantheonComment">or not (1) secret inputs are read from disk, (2) any mpc protocols are</span>
<span class="pantheonComment">executed, and (3) what parties learned the results of mpc. In particular, if a</span>
<span class="pantheonComment">function has no effect, we know none of these things have happened inside the</span>
<span class="pantheonComment">function, and we may decide it's not worth our time to audit (from a security</span>
<span class="pantheonComment">perspective). I realize this isn't the whole story, e.g., we may be crucially</span>
<span class="pantheonComment">depending on the functionality of some library function to have the correct</span>
<span class="pantheonComment">ideal functionality, but the idea is here, and we can keep it around and</span>
<span class="pantheonComment">discuss or drop it.</span>

<span class="pantheonComment">The return type is `𝔹{yshare:A,B}` which reads as “a boolean which is encrypted</span>
<span class="pantheonComment">and recoverable by `A` and `B` by combining encrypted values (e.g., secret</span>
<span class="pantheonComment">shares), and readily embeddible inside a future circuit which is later executed</span>
<span class="pantheonComment">using yao”. Basically this function has decided to execute the circuit `cmp`</span>
<span class="pantheonComment">using yao, and what comes back is like a secret share, and it can either be</span>
<span class="pantheonComment">revealed, or embedded inside a future yao computation.</span>

<span class="pantheonComment">Although this doesn't occur in this example file, suppose you took two values</span>
<span class="pantheonComment">`a,b : 𝔹{yshare:A,B}` and xor'd them like so `a ⊕ b`. The resulting type would</span>
<span class="pantheonComment">be `𝔹{bcir:yshare:A,B}`, that is, a circuit with boolean operations and</span>
<span class="pantheonComment">embedded yao encrypted values. Maybe we should just call this `𝔹{ycir:A,B}`,</span>
<span class="pantheonComment">because the only protocol it makes sense to run it with is yao.</span>

<span class="pantheonComment">The first step of `cmp-mpc` enters parallel mode for both `A` and `B` by the</span>
<span class="pantheonComment">syntax `{A,B}`. The read operation will see a local file &quot;e1-input.txt&quot; for</span>
<span class="pantheonComment">each party `A` and `B`. In our simulator, these live in `examples-data/A` and</span>
<span class="pantheonComment">`examples-data/B`. The result is an `isec:A,B` which again means “independent</span>
<span class="pantheonComment">secrets for both A and B”.</span>

<span class="pantheonComment">The final step of `cmp-mpc` executes the circuit constructed by `cmp xy` using</span>
<span class="pantheonComment">`yao` between parties `A` and `B`. We could have written, e.g., `mpc{yao:C,D}`</span>
<span class="pantheonComment">which would have resulted in (1) A and B send secret-shares of their inputs to</span>
<span class="pantheonComment">C and D, (2) C and D execute yao protocol, and (3) C and D end up with</span>
<span class="pantheonComment">(secret-share) encrypted results which can later be revealed.</span>
<span class="pantheonComment">-}</span>
<span class="pantheonKeyword">def</span> cmp-mpc <span class="pantheonPunctuation">:</span> <span class="pantheonPrimitive">𝟙</span> <span class="pantheonPunctuation">→{</span><span class="pantheonPrimitive">inp</span><span class="pantheonPunctuation">:</span>A<span class="pantheonPunctuation">,</span>B<span class="pantheonPunctuation">;</span><span class="pantheonPrimitive">rev</span><span class="pantheonPunctuation">:}</span> <span class="pantheonPrimitive">𝔹</span><span class="pantheonPunctuation">{</span><span class="pantheonPrimitive">yshare</span><span class="pantheonPunctuation">:</span>A<span class="pantheonPunctuation">,</span>B<span class="pantheonPunctuation">}</span>
<span class="pantheonKeyword">def</span> cmp-mpc <span class="pantheonPunctuation">=</span> <span class="pantheonKeyword">λ</span> <span class="pantheonOperator">•</span> <span class="pantheonPunctuation">→</span>
  <span class="pantheonKeyword">let</span> xy <span class="pantheonPunctuation">:</span> <span class="pantheonPrimitive">ℤ</span><span class="pantheonPunctuation">[</span><span class="pantheonLiteral">64</span><span class="pantheonPunctuation">]{</span><span class="pantheonPrimitive">isec</span><span class="pantheonPunctuation">:</span>A<span class="pantheonPunctuation">,</span>B<span class="pantheonPunctuation">}</span>
  <span class="pantheonKeyword">let</span> xy <span class="pantheonPunctuation">=</span> <span class="pantheonPunctuation">{</span>A<span class="pantheonPunctuation">,</span>B<span class="pantheonPunctuation">}</span> <span class="pantheonPrimitive">read</span><span class="pantheonPunctuation">[</span><span class="pantheonPrimitive">ℤ</span><span class="pantheonPunctuation">[</span><span class="pantheonLiteral">64</span><span class="pantheonPunctuation">]]</span> <span class="pantheonLiteral">&quot;e1-input.txt&quot;</span>
  <span class="pantheonKeyword">let</span> r <span class="pantheonPunctuation">:</span> <span class="pantheonPrimitive">𝔹</span><span class="pantheonPunctuation">{</span><span class="pantheonPrimitive">yshare</span><span class="pantheonPunctuation">:</span>A<span class="pantheonPunctuation">,</span>B<span class="pantheonPunctuation">}</span>
  <span class="pantheonKeyword">let</span> r <span class="pantheonPunctuation">=</span> <span class="pantheonKeyword">mpc</span><span class="pantheonPunctuation">{</span><span class="pantheonPrimitive">yao</span><span class="pantheonPunctuation">:</span>A<span class="pantheonPunctuation">,</span>B<span class="pantheonPunctuation">}</span> cmp xy
  <span class="pantheonKeyword">in</span> r

<span class="pantheonComment">{-</span>
<span class="pantheonComment">`cmp-mpc-rev` run `cmp-mpc` and then reveals the result to each other. Here the</span>
<span class="pantheonComment">`reveal` expression takes as input `𝔹{yshare:A,B}` and returns as output</span>
<span class="pantheonComment">`𝔹{ssec:A,B}`. Just as with `mpc`, you could write `reveal{C,D}` and the</span>
<span class="pantheonComment">meaning of that program is that `A` and `B` send their shares to both `C` and</span>
<span class="pantheonComment">`D`, who then recombine them to learn the result.</span>
<span class="pantheonComment">-}</span>

<span class="pantheonKeyword">def</span> cmp-mpc-rev <span class="pantheonPunctuation">:</span> <span class="pantheonPrimitive">𝟙</span> <span class="pantheonPunctuation">→{</span><span class="pantheonPrimitive">inp</span><span class="pantheonPunctuation">:</span>A<span class="pantheonPunctuation">,</span>B<span class="pantheonPunctuation">;</span><span class="pantheonPrimitive">rev</span><span class="pantheonPunctuation">:</span>A<span class="pantheonPunctuation">,</span>B<span class="pantheonPunctuation">}</span> <span class="pantheonPrimitive">𝔹</span><span class="pantheonPunctuation">{</span><span class="pantheonPrimitive">ssec</span><span class="pantheonPunctuation">:</span>A<span class="pantheonPunctuation">,</span>B<span class="pantheonPunctuation">}</span>
<span class="pantheonKeyword">def</span> cmp-mpc-rev <span class="pantheonPunctuation">=</span> <span class="pantheonKeyword">λ</span> <span class="pantheonOperator">•</span> <span class="pantheonPunctuation">→</span>
  <span class="pantheonKeyword">let</span> r <span class="pantheonPunctuation">:</span> <span class="pantheonPrimitive">𝔹</span><span class="pantheonPunctuation">{</span><span class="pantheonPrimitive">yshare</span><span class="pantheonPunctuation">:</span>A<span class="pantheonPunctuation">,</span>B<span class="pantheonPunctuation">}</span>
  <span class="pantheonKeyword">let</span> r <span class="pantheonPunctuation">=</span> cmp-mpc <span class="pantheonOperator">•</span>
  <span class="pantheonKeyword">let</span> p <span class="pantheonPunctuation">:</span> <span class="pantheonPrimitive">𝔹</span><span class="pantheonPunctuation">{</span><span class="pantheonPrimitive">ssec</span><span class="pantheonPunctuation">:</span>A<span class="pantheonPunctuation">,</span>B<span class="pantheonPunctuation">}</span>
  <span class="pantheonKeyword">let</span> p <span class="pantheonPunctuation">=</span> <span class="pantheonKeyword">reveal</span><span class="pantheonPunctuation">{</span>A<span class="pantheonPunctuation">,</span>B<span class="pantheonPunctuation">}</span> r
  <span class="pantheonKeyword">in</span> p

<span class="pantheonComment">{-</span>
<span class="pantheonComment">`main` just runs `cmp-mpc-rev` to completion. Running this example shows the</span>
<span class="pantheonComment">result of `main`</span>
<span class="pantheonComment">-}</span>
<span class="pantheonKeyword">def</span> main <span class="pantheonPunctuation">:</span> <span class="pantheonPrimitive">𝔹</span><span class="pantheonPunctuation">{</span><span class="pantheonPrimitive">ssec</span><span class="pantheonPunctuation">:</span>A<span class="pantheonPunctuation">,</span>B<span class="pantheonPunctuation">}</span>
<span class="pantheonKeyword">def</span> main <span class="pantheonPunctuation">=</span> cmp-mpc-rev <span class="pantheonOperator">•</span>

</pre>
</body>
</html>
<!-- vim: set foldmethod=manual : -->
