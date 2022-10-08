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
\newunicodechar{∷}{\ensuremath{\mathnormal\Colon}}
\newunicodechar{∨}{\ensuremath{\mathnormal\vee}}
\newunicodechar{ℕ}{\ensuremath{\mathbb{N}}}
\newunicodechar{∈}{\ensuremath{\mathnormal\in}}
\newunicodechar{≡}{\ensuremath{\mathnormal\equiv}}
\newunicodechar{⟩}{\ensuremath{\mathnormal\rangle}}
\newunicodechar{∶}{\ensuremath{\mathnormal\colon\!\!}}
\newunicodechar{∀}{\ensuremath{\mathnormal\forall}}
\newunicodechar{′}{\ensuremath{\mathnormal\prime}}
\newunicodechar{⊤}{\ensuremath{\mathnormal\top}}
\newunicodechar{∘}{\ensuremath{\mathnormal\circ}}
\newunicodechar{ᵇ}{\ensuremath{^\textrm{b}}}

\title{le me'oi .agdalicious. me'oi .implementation.\ be lo fancu be lo rarna'u bei lo'i me'oi .boolean.\ bei le su'u go jetnu gi lo me'oi .input.\ cu mu'oi glibau.\ happy number .glibau.}
\author{la .varik.\ .VALefor.}

\begin{document}
\maketitle

\begin{code}
{-# OPTIONS --guardedness #-}

open import IO
open import Function
open import Data.Nat
open import Data.Bool
open import Data.Nat.Show
open import Data.Nat.DivMod
open import Data.Unit.Polymorphic
open import Data.Char using (isDigit)
open import Data.List hiding (fromMaybe)
open import Data.String using (String; toList)
open import Data.Maybe using (Maybe; maybe′; just; nothing)
\end{code}

\section{la'o zoi.\ \texttt{\$} .zoi.}
ni'o lo nu pilno la'oi .\texttt{\$}.\ cu filri'a lo nu na pilno lo me'oi
.parenthesis.

\begin{code}
ℕ↑ : ℕ → List ℕ
ℕ↑ n = reverse $ ℕ↓ n
  where
  ℕ↓ : ℕ → List ℕ
  ℕ↓ 0 = 0 ∷ []
  ℕ↓ (suc n) = suc n ∷ ℕ↓ n
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

\section{la'oi .\texttt{dsl}.}

ni'o la'o zoi.\ \texttt{dsl n} .zoi.\ liste ko'a goi lo grisumji be lo'i ro kurtenfa be lo'i ro me'oi .digit.\ poi pagbu la'oi .\texttt{n}.\ ge'u je lo grisubji be lo'i ro kurtenfa be lo'i ro me'oi .digit.\ poi pagbu la'oi ko'a be'o je zo'e

.i le mu'oi glibau. termination checker .glibau. cu tolnei  .i ku'i je'a me'oi .terminate. ki'u le nu la'o zoi. ds n .zoi. mleca jo nai dunli la'oi .n.

\begin{code}
{-# TERMINATING #-}
dsl : ℕ → List ℕ
dsl n = dsl' $ n ∷ []
  where
  dsl' : List ℕ → List ℕ
  dsl' [] = []
  dsl' (x ∷ xs) = if ∈2 (x ∷ xs) then xs else dsl' (ds x ∷ x ∷ xs)
\end{code}

\section{la'o zoi.\ ∶⟩ .zoi.}

ni'o go la'o zoi.\ \texttt{∶⟩ n} .zoi.\ jetnu gi la'oi .\texttt{n}.\ mu'oi glibau.\ happy number .glibau.

\begin{code}
∶⟩ : ℕ → Bool
∶⟩ n = 1 ∈ (dsl n)
\end{code}

\section{la'oi .\texttt{getNum}.}
ni'o la'oi .\texttt{getNum}.\ gonai me'oi .just. kacna'u je cu se tcidu fi le mu'oi glibau. standard input .glibau.\ gi me'oi .nothing.

\begin{code}
{-# TERMINATING #-}
getNum : IO (Maybe ℕ)
getNum = readMaybe 10 <$> getLine
\end{code}

\section{la'oi .\texttt{pih}.}
ni'o gonai ge la'oi .\texttt{n}.\ mu'oi glibau.\ happy number .glibau.\ gi ganai co'e ko'a goi zoi zoi.\ \texttt{pih n} .zoi.\ gi lo nu jmina la'oi .\texttt{n}.\ je lo me'oi .newline.\ lo mu'oi glibau.\ standard output .glibau.\ gi ganai co'e ko'i gi me'oi .noop.

\begin{code}
pih : ∀ {a} → ℕ → IO {a} ⊤
pih Q = if ∶⟩ Q then putStrLn (show Q) else return tt
\end{code}

\begin{code}
main : Main
main = run $ getNum >>= maybe′ (IO.List.mapM′ pih ∘ ℕ↑) (pure tt)
\end{code}
\end{document}
