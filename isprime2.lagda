\documentclass{article}

\usepackage{ar}
\usepackage[bw]{agda}
\usepackage{ifsym}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{parskip}
\usepackage{mathabx}
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
\newunicodechar{⊹}{\ensuremath{\mathnormal\dag}}
\newunicodechar{𝕗}{\ensuremath{\mathbb{f}}}
\newunicodechar{ℙ}{\ensuremath{\mathbb{P}}}
\newunicodechar{◆}{\ensuremath{\mathnormal\blackdiamond}}
\newunicodechar{∸}{\ensuremath{\mathnormal\dotdiv}}
\newunicodechar{ᵇ}{\ensuremath{^\mathrm{b}}}
\newunicodechar{≥}{\ensuremath{\mathnormal{≥}}}
\newunicodechar{ϕ}{\textrm\phi}
\newunicodechar{∣}{\ensuremath{\mathnormal{|}}}
\newunicodechar{⁇}{\ensuremath{\mathrm{?\!?}}}


\begin{document}
\section{le me'oi .preamble.}
\begin{code}
{-# OPTIONS --guardedness #-}

open import Data.Nat
open import Data.Bool
open import Data.List
open import Data.Nat.DivMod
\end{code}

\section{la'oi .\texttt{\$}.}
ni'o la'o zoi.\ \texttt{a \$ b} .zoi.\ du la'o zoi.\ \texttt{a b} .zoi.  .i lo nu co'e la'oi .\texttt{\$}.\ cu filri'a lo nu na pilno lo me'oi .parenthesis.

\begin{code}
_$_ : {A : Set} → {B : Set} → (A → B) → A → B
a $ b = a b
infixr 0 _$_
\end{code}

\section{la'oi .\texttt{bool}.}
ni'o gonai ge la'oi .\texttt{c}.\ jetnu gi ko'a goi la'o zoi.\ \texttt{bool a b c} .zoi.\ du la'oi .\texttt{b}.\ gi ko'a du la'oi .\texttt{a}.
\begin{code}
bool : {A : Set} → A → A → Bool → A
bool a b false = a
bool a b true = b
\end{code}

\section{la'oi .\texttt{conq}.}

\begin{code}
conq : {A : Set} → List (List A) → List A
conq t = foldr _++_ [] t
\end{code}

\section{la'oi .\texttt{conqMap}.}

\begin{code}
conqMap : {A : Set} → {B : Set} → (A → List B) → List A → List B
conqMap f x = conq $ map f x
\end{code}

\section{la'oi .\texttt{\#}.}

\begin{code}
# : {A : Set} → List A → ℕ
# [] = 0
# (x ∷ xs) = 1 + # xs
\end{code}

\section{la'o zoi.\ ∅≡ .zoi.}
ni'o go la'o zoi.\ \texttt{∅≡ n} .zoi.\ gi la'oi .\texttt{n}.\ vasru no da

\begin{code}
∅≡ : {A : Set} → List A → Bool
∅≡ t = # t ≡ᵇ 0
\end{code}

\section{la'oi .\texttt{↓}.}
ni'o la'o zoi.\ \texttt{a ↓ b} .zoi.\ liste lo romoi pe'a selvau be la'oi .\texttt{b}.\ je cu se nilzilcmi li su'e ni'e vujnu be lo nilzilcmi be la'oi .\texttt{b}.\ be'o bei la'oi .\texttt{a}.  .i krasi cnici

\begin{code}
_↓_ : {A : Set} → ℕ → List A → List A
0 ↓ xs = xs
n ↓ [] = []
(suc n) ↓ (x ∷ xs) = n ↓ xs
\end{code}

\section{la'oi .\texttt{↑}.}
ni'o la'o zoi.\ \texttt{a ↑ b} .zoi.\ liste lo pamoi pe'a selvau be la'oi .\texttt{b}.\ je cu se nilzilcmi li su'e ni'e vujnu be lo nilzilcmi be la'oi .\texttt{b}.\ be'o bei la'oi .\texttt{a}.  .i krasi cnici

\begin{code}
_↑_ : {A : Set} → ℕ → List A → List A
0 ↑ xs = xs
n ↑ [] = []
(suc n) ↑ (x ∷ xs) = x ∷ (n ↑ xs)
\end{code}

\section{la'oi .\texttt{ϕ}.}

\begin{code}
ϕ : {A : Set} → List A → List A
ϕ χ = ϕ' χ []
  where
  ϕ' : {A : Set} → List A → List A → List A
  ϕ' [] yx = yx
  ϕ' (x ∷ xs) yx = ϕ' xs $ x ∷ yx
\end{code}

\section{la'oi .\texttt{lc}.}

\begin{code}
lc : {A : Set} → (A → A → Bool) → List A → List A → Bool
lc f [] [] = true
lc f [] (b ∷ bx) = false
lc f (a ∷ ax) [] = false
lc f (a ∷ ax) (b ∷ bx) = (f a b) ∧ (lc f ax bx)
\end{code}

\section{la'oi .\texttt{filter'}.}

\begin{code}
filter' : {A : Set} → (A → Bool) → List A → List A
filter' p [] = []
filter' p (x ∷ xs) with p x
...                   | true  = x ∷ filter' p xs
...                   | false = filter' p xs
\end{code}

\section{la'oi .\texttt{listOr}.}
ni'o go nai ge la'oi .\texttt{b}.\ vasru no da gi ko'a goi la'o zoi.\ \texttt{listOr a []} .zoi.\ du la'oi .\texttt{a}.\ gi ko'a remoi selvau la'oi .\texttt{b}.

\begin{code}
listOr : {A : Set} → A → List A → A
listOr x [] = x
listOr x (y ∷ yx) = y
\end{code}

\section{la'o zoi.\ \texttt{>ᵇ} .zoi.}
ni'o go la'o zoi.\ \texttt{a >ᵇ b} .zoi.\ jetnu gi la'oi .\texttt{a} zmadu la'oi .\texttt{b}.

\begin{code}
_>ᵇ_ : ℕ → ℕ → Bool
0 >ᵇ b = false
(suc a) >ᵇ 0 = true
(suc a) >ᵇ (suc b) = a >ᵇ b
\end{code}

\section{la'o zoi.\ \texttt{≥ᵇ} .zoi.}
ni'o go la'o zoi.\ \texttt{a ≥ᵇ b} .zoi.\ jetnu gi la'oi .\texttt{a}.\ dubjavmau la'oi .\texttt{b}.

\begin{code}
_≥ᵇ_ : ℕ → ℕ → Bool
a ≥ᵇ b = (a >ᵇ b) ∨ (a ≡ᵇ b)
\end{code}

\section{la'o zoi.\ \texttt{ℕ↑} .zoi.}
ni'o la'o zoi.\ \texttt{ℕ↓ n} .zoi.\ to'e zmaduse je cu liste lo mulna'u poi mleca ja dunli la'oi .\texttt{n}.\ je cu se nilzilcmi lo sumji be la'oi .\texttt{n}.\ bei li pa

\begin{code}
ℕ↓ : ℕ → List ℕ
ℕ↓ 0 = 0 ∷ []
ℕ↓ (suc n) = suc n ∷ ℕ↓ n
\end{code}

\section{la'o zoi.\ \texttt{ℕ↑} .zoi.}
ni'o la'o zoi.\ \texttt{ℕ↑ n} .zoi.\ zmaduse je cu liste lo mulna'u poi mleca ja dunli la'oi .\texttt{n}.\ je cu se nilzilcmi lo sumji be la'oi .\texttt{n}.\ bei li pa

\begin{code}
ℕ↑ : ℕ → List ℕ
ℕ↑ n = ϕ $ ℕ↓ n
\end{code}

\begin{code}
_◆_ : ℕ → ℕ → ℕ
a ◆ 0 = 0
a ◆ (suc b) = listOr 0 $ filter' (λ c → (c * suc b) ≥ᵇ a) $ ℕ↑ a
\end{code}

\section{la'o zoi.\ \texttt{∣} .zoi.}
ni'o go nai la'o zoi.\ \texttt{a ∣ b} .zoi.\ jetnu gi dilcu la'oi .\texttt{b}.\ la'oi .\texttt{a}.\ li no

\begin{code}
_∣_ : ℕ → ℕ → Bool
n ∣ m = not $ ∅≡ $ filter' (λ x → x * n ≡ᵇ m) $ ℕ↓ m
\end{code}

\begin{code}
𝕗 : ℕ → List ℕ
𝕗 t = filter' (λ x → x ∣ t) $ 2 ↓ ℕ↑ (t ∸ 1)
\end{code}

\section{la'o zoi.\ \texttt{ℙ⁇} .zoi.}
ni'o go la'o zoi.\ \texttt{ℙ⁇ n} .zoi.\ jetnu gi la'oi .\texttt{n}.\ mulna'usle

\begin{code}
ℙ⁇ : ℕ → Bool
ℙ⁇ n = ∅≡ $ 𝕗 n
\end{code}

\section{la'o zoi.\ \texttt{1ℙ>} .zoi.}
ni'o la'o zoi.\ \texttt{1ℙ> n} .zoi.\ to'e traji fo lo'i mulna'usle poi zmadu la'oi .\texttt{n}.

\begin{code}
{-# TERMINATING #-}
1ℙ> : ℕ → ℕ
1ℙ> n = 1ℙ>' n (n + 1)
  where
  1ℙ>' : ℕ → ℕ → ℕ
  1ℙ>' n m = if ℙ⁇ m then m else 1ℙ>' n (suc m)
\end{code}

\section{la'o zoi.\ \texttt{↑ℙ} .zoi.}
ni'o la'o zoi.\ \texttt{↑ℙ n} .zoi.\ liste lo'i remoi pe'a me'oi .prime.\ ku poi se nilzilcmi la'oi .\texttt{n}.

\begin{code}
↑ℙ : ℕ → List ℕ
↑ℙ n = ↑ℙ' n []
  where
  ↑ℙ' : ℕ → List ℕ → List ℕ
  ↑ℙ' 0 x = x
  ↑ℙ' (suc n) [] = ↑ℙ' n $ 2 ∷ []
  ↑ℙ' (suc n) (x ∷ xs) = ↑ℙ' n $ 1ℙ> x ∷ x ∷ xs
\end{code}

\section{la'o zoi.\ \texttt{-𝕗} .zoi.}
ni'o la'o zoi.\ \texttt{-𝕗 n} .zoi.\ to'e traji fo lo'i se dilcymu'o be la'oi .\texttt{n}.

\begin{code}
-𝕗 : ℕ → ℕ
-𝕗 n = listOr n $ 1 ↑ (𝕗 n)
\end{code}

\section{la'o zoi.\ \texttt{/-𝕗} .zoi.}
ni'o la'o zoi.\ \texttt{/-𝕗 n} .zoi.\ dilcu la'oi .\texttt{n}.\ lo to'e traji be fo lo'i se dilcymu'o be la'oi .\texttt{n}.

\begin{code}
/-𝕗 : ℕ → ℕ
/-𝕗 0 = 0
/-𝕗 n = n ◆ (-𝕗 n)
\end{code}

\section{la'o zoi.\ \texttt{𝕗²} .zoi.}
ni'o go nai ge la'oi .\texttt{n}.\ .zoi.\ mulna'usle gi ko'a goi la'o zoi.\ \texttt{𝕗² n} .zoi.\ du la'oi .\texttt{n}.\ gi ko'a liste je cu vasru lo to'e traji be fo lo'i se dilcymu'o be la'oi .\texttt{n}.\ be'o be'o je lo dilcu be la'oi .\texttt{n}.\ bei lo to'e traji be fo lo'i se dilcymu'o be la'oi .\texttt{n}.

\begin{code}
𝕗² : ℕ → List ℕ
𝕗² n = if ℙ⁇ n then n ∷ [] else /-𝕗 n ∷ (-𝕗 n ∷ [])
\end{code}

\section{la'o zoi.\ \texttt{𝕗⊹} .zoi.}
ni'o la'o zoi.\ \texttt{f⊹ n} .zoi.\ liste lo'i mulna'usle ku poi se gripi'i la'oi .\texttt{n}.

\begin{code}
{-# TERMINATING #-}
𝕗⊹ : ℕ → List ℕ
𝕗⊹ n = bool (conqMap 𝕗⊹ (/-𝕗 n ∷ (-𝕗 n ∷ []))) (n ∷ []) $ ℙ⁇ n
\end{code}
\end{document}
