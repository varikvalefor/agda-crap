\documentclass{article}

\usepackage{ar}
\usepackage[bw]{agda}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{parskip}
\usepackage{unicode-math}
\usepackage{newunicodechar}


% \setmathfont{XITS Math}
\newunicodechar{λ}{\ensuremath{\mathnormal\lambda}}
\newunicodechar{∃}{\ensuremath{\mathnormal\exists}}
\newunicodechar{∄}{\ensuremath{\mathnormal\nexists}}
\newunicodechar{∷}{\ensuremath{\mathnormal\Colon}}
\newunicodechar{∨}{\ensuremath{\mathnormal\vee}}
\newunicodechar{ℕ}{\ensuremath{\mathbb{N}}}
\newunicodechar{∈}{\ensuremath{\mathnormal\in}}
\newunicodechar{≡}{\ensuremath{\mathnormal\equiv}}
\newunicodechar{⟩}{\ensuremath{\mathnormal\rangle}}
\newunicodechar{∶}{\ensuremath{\mathnormal\colon\!\!}}
\newunicodechar{ᵇ}{\ensuremath{^\textrm{b}}}

\title{le me'oi .agdalicious. me'oi .implementation.\ be lo fancu be lo rarna'u bei lo'i me'oi .boolean.\ bei le su'u go jetnu gi lo me'oi .input.\ cu mu'oi glibau.\ happy number .glibau.}
\author{la .varik.\ .VALefor.}

\begin{document}
\maketitle

\begin{code}
open import Data.Nat
open import Data.Bool
open import Data.List
open import Data.Nat.DivMod
\end{code}

\section{la'o zoi.\ \texttt{\$} .zoi.}
ni'o lo nu pilno la'oi .\texttt{\$}.\ cu filri'a lo nu na pilno lo me'oi
.parenthesis.

\begin{code}
_$_ : {A B : Set} → (A → B) → A → B
a $ b = a b
infixr 1 _$_
\end{code}

\section{la'o zoi.\ \texttt{∃} .zoi.}
ni'o go la'o zoi.\ \texttt{∃ p x} .zoi.\ jetnu gi la'oi .\texttt{x}.\ vasru zo'e poi ke'a goi la'oi .\texttt{a}.\ zo'u la'o zoi.\ \texttt{p a} .zoi.\ jetnu

\begin{code}
∃ : {A : Set} → (A → Bool) → List A → Bool
∃ p [] = false
∃ p (x ∷ xs) = (p x) ∨ (∃ p xs)
\end{code}

\section{la'o zoi.\ \texttt{∄} .zoi.}
ni'o go la'o zoi.\ \texttt{∄ p x} .zoi.\ jetnu gi la'oi .\texttt{x}.\ na vasru zo'e poi ke'a goi la'oi .\texttt{a}.\ zo'u la'o zoi.\ \texttt{p a} .zoi.\ jetnu

\begin{code}
∄ : {A : Set} → (A → Bool) → List A → Bool
∄ p xs = not (∃ p xs)
\end{code}

\section{la'o zoi.\ \texttt{∈} .zoi.}
ni'o go la'o zoi.\ \texttt{a ∈ b} .zoi.\ jetnu gi la'oi .\texttt{a}.\ cmima la'oi .\texttt{b}.

\begin{code}
_∈_ : ℕ → List ℕ → Bool
a ∈ [] = false
a ∈ (b ∷ bs) = (a ≡ᵇ b) ∨ (a ∈ bs)
\end{code}

\section{la'o zoi.\ \texttt{∈2} .zoi.}
ni'o go la'o zoi.\ \texttt{∈2 k} .zoi.\ gi pa da xi pa zo'u pa da xi re zo'u la'oi .\texttt{k}.\ vasru da xi pa je da xi re

\begin{code}
∈2 : List  ℕ → Bool
∈2 [] = false
∈2 (x ∷ xs) = (x ∈ xs) ∨ (∈2 xs)
\end{code}

\section{la'oi .\texttt{digits}.}
ni'o la'o zoi.\ \texttt{digits n} .zoi.\ liste lo me'oi .digit.\ poi pagbu la'oi .\texttt{n}.

.i la'oi .\texttt{digits}.\ me'oi .terminate.\ ni'i le nu ganai la'oi .\texttt{digits'}.\ me'oi .terminate.\ gi la'oi .\texttt{digits}.\ me'oi .terminate.\ kei je le nu ge ganai la'o zoi.\ \texttt{n div 10} .zoi.\ du li no ja cu mleca la'oi .\texttt{n}.\ gi la'oi .\texttt{digits'}.\ me'oi .terminate.\ gi la'o zoi.\ \texttt{n div 10} .zoi.\ du li no ja cu mleca la'oi .\texttt{n}.  .i ku'i le te samrkompli cu xlabebna je cu na jimpe le du'u la'oi .\texttt{digits'}.\ me'oi .terminate.

.i cumki fa lo nu xamgu fa lo nu da'i la'oi .\texttt{digits}.\ binxo zo'e poi ke'a goi ko'a zo'u le te samrkompli cu jimpe le du'u ko'a me'oi .terminate.

\begin{code}
{-# TERMINATING #-}
digits : ℕ → List ℕ
digits n = digits' n []
  where
  digits' : ℕ → List ℕ → List ℕ
  digits' 0 xs = xs
  digits' n xs = digits' (n div 10) $ n % 10 ∷ xs
\end{code}

\section{la'oi .\texttt{ds}.}

ni'o la'o zoi.\ \texttt{ds n} .zoi.\ grisumji lo'i kurtenfa be lo'i me'oi .digit.\ be la'oi .\texttt{n}.

.i la'o zoi.\ \texttt{ds n} .zoi.\ mleca jo nai dunli la'oi .\texttt{n}.

\begin{code}
ds : ℕ → ℕ
ds n = sum $ map (λ t → t ^ 2) $ digits n
\end{code}

\section{la'oi .\texttt{dsl'}.}
ni'o la'oi .\texttt{dsl'}.\ me'oi .helper.\ fancu la'oi .\texttt{dsl}.

.i le mu'oi glibau. termination checker .glibau. cu tolnei  .i ku'i je'a me'oi .terminate. ki'u le nu la'o zoi. ds n .zoi. mleca jo nai dunli la'oi .n.

\begin{code}
{-# TERMINATING #-}
dsl' : List ℕ → List ℕ
dsl' [] = []
dsl' (x ∷ xs) = if ∈2 (x ∷ xs) then xs else dsl' (ds x ∷ x ∷ xs)
\end{code}

\section{la'oi .\texttt{dsl}.}

ni'o la'o zoi.\ \texttt{dsl n} .zoi.\ liste ko'a goi lo grisumji be lo'i ro kurtenfa be lo'i ro me'oi .digit.\ poi pagbu la'oi .\texttt{n}.\ ge'u je lo grisubji be lo'i ro kurtenfa be lo'i ro me'oi .digit.\ poi pagbu la'oi ko'a be'o je zo'e

\begin{code}
dsl : ℕ → List ℕ
dsl n = dsl' $ n ∷ []
\end{code}

\section{la'o zoi.\ ∶⟩ .zoi.}

ni'o go la'o zoi.\ \texttt{∶⟩ n} .zoi.\ jetnu gi la'oi .\texttt{n}.\ mu'oi glibau.\ happy number .glibau.

\begin{code}
∶⟩ : ℕ → Bool
∶⟩ n = 1 ∈ (dsl n)
\end{code}
\end{document}
