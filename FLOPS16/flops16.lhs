\documentclass{llncs}
\usepackage[english]{babel}
\usepackage{amsmath}
%\usepackage{amsthm}
\usepackage{amsfonts}
%\usepackage{proof}
\usepackage[usenames,dvipsnames]{color}
\usepackage[all]{xy}
\usepackage{wrapfig}
\usepackage{bussproofs}
\usepackage{bbold}
\usepackage{tikz}
\usepackage{tikz-qtree}

%format PP = "\mathbb{P}"
%format RR r a b = "{" b "}\xleftarrow{" r "}{" a "}"
%format ><  = "\times"
%format all = "\forall"
%format <<  = "\subseteq"
%format <== = "\Leftarrow"
%format ==r = "\equiv_r"
%format === = "\equiv"
%format ===n = "\not\equiv"
%format ~==  = "\approx"
%format BOT = "\bot"
%format bn  = "\mathbb{N}"
%format Unit = "\mathbb{1}"
%format Either a b = "{" a "} + {" b "}"
%format MP  = "\mathbb{MP}"
%format i2 = "i_2"
%format *  = "\times"
%format <<-antisym = "\subseteq\hspace{-.5mm}-\text{antisym}"

%format forall = "\forall"
%format ==     = "\equiv"
%format =|    = "\equiv\hspace{-1.5mm}\langle"
%format |=    = "\rangle"
%format |=*    = "\rangle^\star"
%format qed   = "\square"

%format Nat   = "\mathbb{N}"
%format bot = "\bot"

%format :: = ":\vspace{-1mm}:"

\newenvironment{TODO}{%
  \color{blue} \itshape \begin{itemize}
}{%
  \end{itemize}
}

\newcommand{\warnme}[1]{{\color{red} \textbf{$[$} #1 \textbf{$]$}}}

\newcommand{\K}[1]{\emph{#1}}
\newcommand{\D}[1]{\emph{#1}}

\title{Term Indexed Tries}

\author{Victor Cacciari Miraldo and Wouter Swierstra}
\institute{University of Utrecht}

%include lhs2TeX.fmt

\begin{document}
\maketitle

\section{Introduction}
\label{sec:introduction}

On \cite{Miraldo2015} we explore the construction of a rewriting engine for Agda \cite{norell07}. 
We use generic programming techniques, and Agda's support for such, to generate the terms
that justify the given rewrite steps. The users needs only to provide the name of the lemma they want to apply.
We are going to illustrate our framework in section \ref{sec:example}. Agda's Reflection
module allows the programmer to access the meta-representation of terms during typechecking.
They can also generate other terms and plug them back in, mid-compilation.

A reader already familiar with Agda might argue that small rewrites are quite simple to perform 
using the \K{rewrite} keyword. When the need to perform equational reasoning over complex formulas 
arises, however, we still need to specify the substitutions manually in order to apply a theorem to a subterm. 
This manual specification is error prone and purely mechanical, as we shall see in this paper.

\begin{TODO}
  \item a bit more glue around and a general rewriting of this, since the structure changed.
\end{TODO}

Even though our framework is capable of figuring out which parameters to apply to the user supplied lemma,
we want to go a step further. What if our framework could find which lemma to apply, given a database
of lemmas? The idea for Term-indexed Tries arises from the need to make such lemma-database efficient,
at least for look up, given that String-indexed Tries are the data-structure of choice for searching substrings.

Working with strings as indexes for a trie, however, is very easy (as their functor is linear on the recursive arguments).
We will see how things get a bit trickier once we start working with generic functors. Another 
stone in the way is how should we handle variables. Theorems and lemmas, especially when defined
on proof-assistants, assume a general form, for instance, right identity for addition states
that for all $x$, $x + 0 = x$. We can instantiate $x$ to anything here. Why does right identity
works for justifying that $\pi \times (r^2 + 0) = \pi \times r^2$? Because there is 
an instantiation, namelly $x \mapsto r^2$, which when applied to the lemma, with congruence $\pi \times \square$,
closes the proof.

Our initial objective was to code this structure for storing lemmas in Agda, and release
it as part of the rewriting framework of \cite{Miraldo2015}. Agda is a pure, functional language
with a dependent type system built on top of the Theory of Types, Martin L\"{o}f, \cite{lof84}.
We refer the reader to \cite{nords90,norell2009} for a good introduction on both the theory and practice of Agda.
Performance problems stoped the development of our Term-Trie in Agda, specially within the insertion function. 
We still need time to properly pinpoint the problem. Taking into account, also, that it is more likely that readers are
familiar with Haskell, we are going to present the datastructures and algorithms
we use in Haskell.

The \emph{agda-rw} library is publicaly available on the internet in the following
GitHub repository.
\begin{quote}
  \url{https://github.com/VictorCMiraldo/agda-rw}
\end{quote}

\section{Basic Agda}
\label{sec:basicagda}

In languages such as Haskell or ML, where a Hindley-Milner based algorithm is used for
type-checking, values and types are clearly separated. Values are the objects being
computed and types are simply tags to \emph{categorize} them. In Agda, however,
this story changes. There is no distinction between types and values, which gives a whole
new level of expressiveness to the programmer. 

The Agda language is based on the intensional theory of types by Martin-L\"{o}f \cite{lof84}.
Great advantages arise from doing so, more specifically in the programs-as-proofs mindset.
Within the Intensional Theory of Types, we gain the ability to formally state the meaning
of quantifiers in a type. We refer the interested reader to \cite{nords90}. 

Datatype definitions in Agda resemble Haskell's GADTs syntax \cite{Jones2006}. Let us
illustrate the language by defining fixed-size Vectors. For this, we need
natural numbers and a notion of sum first.

\vspace{2mm}
\begin{minipage}[t]{0.45\textwidth}
\begin{code}
data Nat : Set where
  Z : Nat
  S : Nat -> Nat
\end{code}
\end{minipage}
\begin{minipage}[t]{0.45\textwidth}
\begin{code}
_ + _ : Nat -> Nat -> Nat
Z + n     = n
(S m) + n = S (m + n)
\end{code}
\end{minipage}
\vspace{2mm}

The |Nat : Set| statement is read as \emph{Nat is of kind $*$}, for the Haskell enthusiast.
In a nutshell, |Set|, or, $\text{Set}_0$, is the first universe, the type of small types. For consistency reasons,
Agda has an infinite number of non-cumulative universes inside one another. That is,
$\text{Set}_i \nsubseteq \text{Set}_i$ but $\text{Set}_i \subseteq \text{Set}_{i+1}$. 


The underscores in the definition of $+$ indicate where each parameter goes. This is how we
define mix-fix operators. We can use underscores virtually anywhere in a declaration, as long
as the number of underscores coincide with the number of parameters the function expects.

\section{Why building a new tactic?}
\label{sec:example}

In order to illustrate the application of the \emph{agda-rw} library, let us consider 
the proof of commutativity, over sum, for natural numbers. The proof itself is very simple,
and as we will witness, two simple lemmas and a induction hypothesis suffice to complete
the proof.

\begin{figure}[h]
\begin{code}
succomm : forall m n -> m + suc n == suc (m + n)
identity : forall n -> n + 0 == n

comm : forall m n -> m + n == n + m
comm zero    n = sym (identity n)
comm (suc m) n =
  begin
    suc m + n
  =| refl |=
    suc (m + n)
  =| cong suc (comm m n) |=*
    suc (n + m)
  =| sym (succomm n m) |=
    n + suc m
  qed
\end{code}
\caption{Addition commutativity over Natural Numbers}
\label{fig:example1}
\end{figure}

Here |==| is Agda Propositional Equality type. Whenever we say |x == y| we mean
that |x| and |y| \emph{evaluate to the same value}. Let us take a more delicate
look on what is going on on the above proof. The first step, $(suc m) + n \equiv suc (m + n)$
is justified by the definition of $+$ in the standard library, therefore they
must evaluate to the same value. The second justification, however, is a congruence.
We can think of this congruence as some sort of context for rewriting. Note how
the rewrite happens inside the $suc$ context. The recursive call models the induction hypothesis.
The last step is pretty straight forward. Here, $sym$ denotes symmetry of $\equiv$.

Note the step marked with a $\cdot^\star$. The term |cong suc (comm m n)| is exactly what
is generated by calling our tactic \D{by}, passing \D{comm} as the lemma we want to apply.
In the rest of this document we will explain how did we accomplish this.

\subsection*{Rewriting in Agda}

During any kind of mathematical reasoning, in a pen-and-paper context, one usually uses 
a fair amount of implicit rewrites. Yet, we cannot skip these steps in a proof assistant.
We need to really convince Agda that two things are equal, by Agda's equality notion, 
before it can syntatically rewrite the terms.

Let us see the definition of Propositional Equality, in Agda. Remembering
that |x == y| means that |x| and |y| evaluate to the same value. This is
enforced by repeating the variable in the type of |refl|.

\hfill
\begin{code}
data _ == _ {A : Set} (x : A) : A -> Set where
    refl : x == x
\end{code}
\hfill
 
Having a proof $p : x \equiv y$ convinces Agda that $x$ and $y$ will \emph{evaluate} to the 
same value. Whenever this is the case, we can rewrite $x$ for $y$ in a 
predicate. The canonical way to do so is using the \emph{subst} function:

\hfill
\begin{code}
subst : {A : Set}(P : A -> Set){x y : A} -> x === y -> P x -> P y
subst P refl p = p
\end{code}
\hfill

\noindent Here, the predicate |P| can be seen as a context where the rewrite will happen.
From a programming point of view, Agda's equality notion makes perfect sense! Yet,
whenever we are working with more abstract concepts, we might need a finer notion
of equality. However, this new equality must agree with Agda's equality if
we wish to perform syntactical rewrites. As we will see in the next section,
this is not always the case.

It is worth mentioning a subtle detail on the definition of |subst|. Note that, on the
left hand side, the pattern |p| has type |P x|, according to the type signature. Still,
Agda accepts this same |p| to finish up the proof of |P y|. What happens here is that
upon pattern matching on |refl|, Agda knows that |x| and |y| evaluate to the same value.
Therefore it basically substitutes, in the current goal, every |y| for |x|. As we can see
here, pattern-matching in Agda actually allows it to infer additional information during
type-checking.

\section{Reflection in Agda}
\label{sec:reflection}

As of version 2.4.8, Agda's reflection API provides a few keywords displayed in table
\ref{tbl:agda_reflection_api}. This feature can the thought of as the Template Haskell
approach in Agda, or, meta programming in Agda. 

The idea is to access the abstract representation of a term, during compile time,
perform computations over it and return the resulting term before resuming compilation.
We will not delve into much detail on Agda's abstract representation. 
The interested reader should go to Paul van der Walt's thesis\cite{vdWalt2012}, where,
although somewhat outdated, Paul gives a in-depth explanation of reflection in Agda.
However, the following excerpt gives a taste of how reflection looks like. 

\vskip 1em
\begin{code}
example : quoteTerm (\ x -> suc x) == con (quote suc) []
example = refl
\end{code}
\vskip 1em

Although very small, it states that the abstract representation of \IC{suc} is a constructor,
whose name is \F{suc} and has no arguments whatsoever. The \D{Term} datatype, exported from
the Reflection module, has a large number of constructors and options. We are just interested
in a small subset of such terms, which is enough motive to build our own term datatype.
That is the reason why we will not explain reflection in depth. Nevertheless, the next
section provides a discussion on our interface to reflection.

Another interesting factor is to note how Agda normalizes a term before quoting it. Note
how it performed a $\eta$-reduction automatically. To prevent this is the reason why we need all those \K{record}
boilerplate in our Relational Algebra library.

\begin{center}
\begin{table}[h]
\begin{tabular}{l l}
  \K{quote} & Returns a \D{Name} datatype, representing the quoted identifier. \\[2mm]
  \K{quoteTerm} & Takes a term, normalizes it and returns it's \D{Term} inhabitant. \\[2mm]
  \K{quoteGoal} g \K{in} f \hskip 1em & Brings a quoted version of the goal in place into $f$'s scope,
                          namely, $g$. \\[2mm]
  \K{quoteContext} & Returns a list of quoted types. This is the ordered list of \\
                   & types of the local variables from where the function was called. \\[2mm]
  \K{tactic} f & Is syntax-sugar for $\K{quoteGoal}\;g\;\K{in}\;(f\;\K{quoteContext}\;g)$.
\end{tabular}
\caption{Agda 2.4.8 Reflection API}
\label{tbl:agda_reflection_api}
\end{table}
\end{center}

The general idea behind \emph{agda-rw} is to use Agda's Reflection API to generate
the congruences and substitutions needed to justify the rewrites we seek to perform,
such as the marked congruence in figure \ref{fig:example1}. In the following
sections we will give a brief explanation of the operations we need to generate
such terms.

\subsection{Terms and Rewriting}

Before some confusion arises it is important to explain that we can not tackle rewriting 
in a standard fashion, like arbitrary term rewriting systems might do.
Our problem is, in fact, slightly different. Given two structurally different terms and
an action, we want to see: (A) if it is possible to apply such action in such a way that (B) it
justifies the rewriting step. The first step is a simple matter of unification, which will be
discussed later. However, the second part, justifying the rewrite, boils down to the generation
of a \F{subst} that explains to Agda that what we are doing is valid. Our main goal here
is to generate such \F{subst}. 

In the Reflection module, Agda provides us with the term-language they use. It is worth
mentioning that their definition is over the top for what we need. We will handle terms
only. No need to worry about half the constructors they provide. For this reason,
we decided to make our own AST. This can also be helpful on the future, if Agda changes its
Reflection interface.

A Term is something in the standard lambda-calculus format. However, we split the base case
in three separate cases. An \emph{ovar} is an outer variable. This provides a way for us
to plug in different types inside a Term. The \emph{ivar} construct represents a DeBruijn indexed
variable. Literals are pretty self-explanatory. 

\vskip 1em
\begin{code}
data RTerm {a}(A : Set a) : Set a where
    ovar : (x : A) -> RTerm A
    ivar : (n : Nat) -> RTerm A
    rlit : (l : Literal) -> RTerm A
    rlam : RTerm A -> RTerm A
    rapp : (n : RTermName)(ts : List (RTerm A)) -> RTerm A
\end{code}
\vskip 1em

Applications, however, need to be distinguished between constructor applications
and definitions. We also add \emph{impl} to represent the arrow type |_ -> _|. 

\vskip 1em
\begin{code}
data RTermName : Set where
    rcon : Name -> RTermName
    rdef : Name -> RTermName
    impl : RTermName
\end{code}
\vskip 1em

One of the advantages of having a parametric Term datatype is the guarantees
that we can provide with it. Specially using a dependent type system. We can
represent closed terms, |RTerm bot|, where |bot| represents the empty type.
We can represent terms with holes using |RTerm (Maybe A)|. We can use the
parameter to plug in additional information needed for specific situations,
for instance, finite indexes for unification, as in \cite{mcbride03}.

We will not delve into the technicalities of converting Agda terms to \K{RTerm}s.
The technique we used was inspired by \emph{Auto in Agda} \cite{Swierstra15}, cf. \cite{Miraldo2015}. 
Given our term AST, we will now illustrate the important operations for: (A) inferring
the context of the rewrite and (B) infering the parameters to pass to the user-supplied lemma.

\begin{TODO}
  \item maybe introduce lists in Agda? I mean, they are the same as in Haskell...
\end{TODO}

Assume one is trying to prove associativity of list concatenation. 
Here, |_ ++ _| denotes the canonical definition of concatenation and |x :: xs| is the
list with |x| as its head and |xs| as its tail.

\vskip 1em
\begin{code}
assoc : forall {xs ys zs} -> (xs ++ ys) ++ zs == xs ++ (ys ++ zs)
assoc nil _ _ = refl
assoc (x :: xs) ys zs = ?
\end{code}
\vskip 1em

The obvious solution to the hole above is |cong (_::_ x) (assoc xs ys zs)|. Basically, the \emph{action}
that fits in the problem is |assoc|, which corresponds to the induction hypothesis. The rest
of the information can be inferred, automatically, from the goal and action type, whose
types are given in figure \ref{fid:goal_act_notation}.

\newcommand{\conc}{|++|}
\newcommand{\cons}{::}
\newcommand{\labelover}[2]{\stackrel{#1 \vspace{1mm}}{#2}}
\begin{figure}[h]
\[
\begin{array}{l c}
    \text{Goal} &
    \underbrace{(x\; \cons\; xs\;\conc\; ys)\; \conc\; zs}_{g_1} \labelover{hd_g}{\equiv} \underbrace{x\;\cons\; xs\;\conc\; (ys\; \conc zs)}_{g_2} \\[0.4cm]
    \text{Action} &
    \underbrace{(xs\;\conc\; ys)\; \conc\; zs}_{a_1} \labelover{hd_a}{\equiv} \underbrace{xs\;\conc\; (ys\; \conc zs)}_{a_2}
\end{array}
\]
\caption{Goal and Action for hole zero}
\label{fig:goal_act_notation}
\end{figure}

Looking at both terms, it is not hard to infer that it is some sort of term-intersection
that is going to give the abstraction (context) to use it as a congruence. If we use 
strucutral intersection, though, we have $g_\square = g_1 \cap g_2 = (x :: \square \conc \square)$,
where $\square$ represents a hole, or the part in which the terms differ. We obtain a term with two 
holes! We should lift definitions whose arguments are all holes, to a single hole.

\[
g_\square = g_1 \cap g_2 = (x \; \cons\; \square\; \conc\; \square) \stackrel{lift}{\rightarrow} (x \; \cons\; \square)
\]

Term intersection and lifting are easily defined by recursion on terms. The type
signature for the aforementioned operations are as follows.

%format cap = "\cap"
%format tlift = "\uparrow"
\vskip 1em
\begin{code}
_ cap _ : {A : Set}{{ eqA : Eq A }} 
        -> RTerm A -> RTerm A -> RTerm (Maybe A)
        
_ tlift : forall {a}{A : Set a} -> RTerm (Maybe A) -> RTerm (Maybe A)
\end{code}
\vskip 1em

Here, we already have ways of infering the context under which the rewrite happens. We
also have the lemma that is going to be applied. Now, it is a matter of figuring out the
parameters that need to be supplied to the lemma.

The context, $g_\square$, can be seen as a road-map. It makes sense to be able
to compute the difference of a given term and $g_\square$. That is,
$g_\square - g_2 \equiv xs \conc (ys \conc zs)$. This operation is defined by
recursion on both terms. While we keep seeing equal  constructors, we keep traversing.
When we find the hole, we return the second term. If a diffence is encountered, we return
|nothing|.

Let us denote the type of our lemma, $assoc$, using De Bruijn indexes.
We have $t = \lambda \lambda \lambda . (0 \conc 1) \conc 2 \equiv 0 \conc (1 \conc 2)$. 
A simple instantiation of $g_\square - g_i$ with $t_i$ yields $\{ 0 \mapsto xs , 1 \mapsto ys , 2 \mapsto zs \}$.
Which is sufficient to generate the term that justifies the rewrite. The substitution 
gives the parameters, in order, that should be applied to the lemma and the term $g_\square$ gives
the context in which the rewrite happens.

\subsection{Library Structure}

Up to this point, we gave a small description of how we accomplish rewrites in Agda. 
Yet, different domains might require different terms. For it is also important to 
outline the structure of the library and its respective API.

One interesting aspect of Agda is the possibility to have parametric modules,
that is, modules that receive parameters when they are imported. 

The top level module is \texttt{\small RW.RW}, and this module receives a list
of \emph{Term Strategies}, or something of type \emph{TStratDB}. This strategy
record specifies both a predicate to indicate when this strategy should be used,
given the goal and lemma topmost relations, and how to construct the final
term given the information computed internally. 

Below we find, verbatim, the strategy provided for reasoning over
propositional equality.

\vskip 1em
\begin{code}
module RW.Strategy.PropEq where

  pattern pat-≡  = (rdef (quote _≡_))

  private
    open UData

    when : RTermName -> RTermName -> Bool
    when pat-≡ pat-≡ = true
    when _     _     = false

    fixTrs : Trs -> RTerm ⊥ -> RTerm ⊥
    fixTrs Symmetry term = rapp (rdef (quote sym)) (term ∷ [])

    how : Name -> UData -> Err StratErr (RTerm ⊥)
    how act (u-data g□ σ trs)
      = i2 (rapp (rdef (quote cong))
                 ( hole2Abs g□
                 :: foldr fixTrs (makeApp act σ) trs
                 :: [])
           )

  propeq-strat : TStrat
  propeq-strat = record
    { when = when
    ; how  = how
    }
\end{code}
\vskip 1em

the \emph{when} predicate specifies that when both topmost relations are the propositional
euality we should use \emph{how} to compute the final term. Whereas \emph{how}
uses the information provided by the backend, which comes through in a record, and
generates the correct congruence. We transform the hole of $g_\square$ into an abstraction,
we append a call to \emph{symmetry} when needed and we apply the substitution's terms
to the action supplied by the user. This is returned as a closed term which is
later on plugged back in by Agda's reflection mechanism.

In order to use the \emph{RW} library with this strategy, one should import it as follows.

\vskip 1em
\begin{code}
open import RW.Strategy.PropEq using (propeq-strat)
open import RW.RW (propeq-strat :: [])
\end{code}
\vskip 1em

Note that \emph{RW.RW} receives a list of strategies, so one can mix them at run-time.


\begin{TODO}
  \item Explain how a user would use the by tactic ith his own relations. Explain the "API".
\end{TODO}

\section{Generalizing}

\begin{TODO}
  \item Mention the generalizations, making space for Term-Indexed tries.
\end{TODO}

\bibliographystyle{alpha}
\bibliography{references}

\end{document}

\section{String-Indexed Tries}
\label{sec:stringtries}

Our data-structure arises as a generalization of Tries. There a few variations of a Trie, suited for different applications. We will, however,
restrict ourselves to the original definition, which is also the simplest. This small digression
has the purpose of introducing the underlying idea without too many technicalities.

%\begin{wrapfigure}{r}{0.35\textwidth}
%%\begin{figure}[h]
%\begin{center}
%\begin{tikzpicture}[
%  cnode/.style={rectangle , draw=black , fill=white},
%  lbl/.style={circle , draw=none , fill=white , inner sep=0cm , font={\tiny \color{blue}}}
%]
%\tikzset{level 0+/.style={level distance=2cm}}
%\Tree [.\node[cnode]{$\epsilon$};
%        \edge node[pos=0.5 , lbl] {t};
%        [.\node[cnode]{t};
%           \edge node[pos=0.5 , lbl] {o};
%           [.\node[cnode]{to};
%             \edge[dashed] node[pos=0.5 , lbl] {tal};
%             [.\node[cnode]{total}; ] 
%           ]
%           \edge node[pos=0.5 , lbl] {e};
%           [.\node[cnode]{te};
%              \edge node[pos=0.5 , lbl] {a};
%              [.\node[cnode]{tea}; ]
%              \edge node[pos=0.5 , lbl] {n};
%              [.\node[cnode]{ten}; ]
%           ] 
%        ]
%      ];
%\end{tikzpicture}
%\end{center}
%\caption{Trie example}
%\label{fig:firsttrie}
%\end{wrapfigure}

Figure \ref{fig:firsttrie} shows a trie that stores the string set 
$S = \{ "t" , "to" , "tot" , "tota" , "total" , \cdots \}$.
A few important notions to note are that, even though it has a tree structure, the keys are
not associated with a specific node, but with its positioning in the trie.
In the end of the day, we can look at Tries as finite deterministic acyclic automatons.

The specification of a Trie is fairly simple. Taking already a small step towards a generalization
and assuming that instead of storing lists of characters (strings) we are going to store arbitrary
lists, the Trie functor is given by:

\[
  T\;a\;k = \mu X . (k + 1) \times (a \rightarrow X + 1)
\]

So, each node contains a possible key, which is isomorphic to a partial map from $1$ to a key, and a partial map from $a$'s to Tries. The retrieval of
the key associated with a list $l$ is performed by recursion on $l$. When we reach the empty list
we return the $(k+1)$ part of the current node. Otherwise, we try to traverse the trie associated with the
current node partial map applied to the head of the list. 

Insertion is also very straight forward. Inserting a key $k$ indexed by a list $l$, assuming $l$ does not belong
in the trie, yet, consists of a walk in the trie, by induction $l$, adding entries to the partial maps, if needed,
until we reach the empty list, and then register $k$ at that node.

The biggest limitation of a Trie, however, is that it can only be indexed by a linear, list-like, data-structure, 
such as a list. R. Hinze, J. Jeuring and A. L\"{o}h provides a solution to that, in \cite{Hinze04}, 
by defining a special kind of Tries that can be indexed by arbitrary data-types. The idea, in a nutshell,
is to work with the algebraic representation of the indexes (data-types) and have nested maps at every node.
This is a bit too general for our needs here. We are looking for a structure that can be indexed
by a given term language, which follows the typical sum-of-products form. An additional complication
arises when we start to allow variables in the index.

\begin{TODO}
  \item Instantiation variables in a string trie is more complicated than variables
        in a term trie. Trie for regexp: "fstXsndX", we need to stop consuming
        chars and backtrack everytime a new char is found, until we finished the string.
        Whereas on term instantiations there is no backing track, as the Trie has more structure.
\end{TODO}

\section{Term-Indexed Tries}
\label{sec:termtries}

Following the popular saying -- A picture is worth a thousand words -- let us begin
with a simple representation. Just like a trie, our RTrie trie was designed to
store names of actions to be performed, indexed by their respective type. Figure 
\ref{fig:btrie1} shows the RTrie that stores the actions from figure \ref{fig:trie1terms}.
For clarity, we have written the De Bruijn indexes of the respective variables as a superscript on
their names.

\begin{figure}[h]
\begin{eqnarray*}
  x^0 + 0 & \equiv & x^0 \\
  x^0 + y^1 & \equiv & y^1 + x^0 \\
  x^2 + (y^1 + z^0) & \equiv & (x^2 + y^1) + z^0
\end{eqnarray*}
\caption{Identity, Commutativity and Associativity for addition.}
\label{fig:trie1terms}
\end{figure}

\begin{figure}[h]
\include{img/BTrie1}
\caption{RTrie for terms of figure \ref{fig:trie1terms}. Yellow and green circles represent DeBruijn indexes and literals, respectively.}
\label{fig:btrie1}
\end{figure}

Let us illustrate the lookup of, for instance, $(2 \times x) + 0 \equiv 2 \times x$.
The search starts by searching in the root's partial map for $\equiv$. We're given
two tries! Since $\equiv^{\star_1}$ is a binary constructor. We proceed by looking for $(2 \times x) + 0$
in the left child of $\equiv$. Well, our topmost operator is now a $+^{\star_2}$, we repeat the same idea and
now, look for $(2 \times x)$ in the left child of the left $+$. Here, we can choose
to instantiate variable 0 as $(2 \times x)$ and collect label $r_1$ or
instantiate variable 2, with the same term, and collect label $l_1$. Since we cannot know beforehand
which variable to instantiate, we instantiate both! At this point, the state of our lookup is
$(0 \mapsto 2 \times x , r_1) \vee (2 \mapsto 2 \times x , l_1)$.
We proceed to look for the literal $0$ in the right trie of $+^{\star_2}$, taking us to a leaf node with
a rewrite rule stating $r_1 \vdash r_2$. This reads $r_1$ should be rewritten by $r_2$. We apply
this to all states we have so far. Those that are not labeled $r_1$ are pruned. 
However, we could also instantiate variable 1 at that node, so
we add a new state $(0 \mapsto 2 \times x, 1 \mapsto 0 , k_1)$. At this step,
our state becomes $(0 \mapsto 2 \times x , r_2) \vee (0 \mapsto 2 \times x, 1 \mapsto 0 , k_1)$. 

We go up one level and find that
now, we should look for $2 \times x$ at the right child of $\equiv^{\star_1}$. We cannot traverse the
right child labeled with a $+$, leaving us with to compare the instantiation gathered for
variable 0 in the left-hand-side of $\equiv^{\star_1}$ to $2 \times x$. They are indeed the same,
which allows us to apply the rule $r_2 \vdash RI$. Which concludes the search, rewriting label $r_2$
by $RI$, or, any other code for \F{+-right-identity}. By returning not only the final label, but
also the environment gathered, we get the instantiation for variables for free.
The result of such search should be $(0 \mapsto 2 \times x , RI) :: []$.

This small worked example already provides a few insights not only on how to code lookup, but
also on how to define our RTrie. We have faced two kinds of nodes. Fork nodes, which
are composed by a list of cells, and, Leaf nodes, which contain a list of (rewrite) rules.

\begin{TODO}
  \item Show the BTrie typeclass, prove that every strictly positive functor
        has an instance.
  \item Picture of a term database
  \item Illustration of a lookup.
\end{TODO}

\subsection{Looking up}
\label{sec:termtries:lookup}

\subsection{Inserting}
\label{sec:termtries:insertion}

\section{Conclusion}
\label{sec:conclusion}




\bibliographystyle{alpha}
\bibliography{references-thesis}

\end{document}


