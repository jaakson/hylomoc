\documentclass[11pt]{article}
\usepackage{calc}
\usepackage{amssymb}
\usepackage{amsfonts}
\usepackage{amsmath}

\newsavebox{\fminibox}
\newlength{\fminilength}
\newenvironment{fminipage}[1][\linewidth]
 {\setlength{\fminilength}{#1-2\fboxsep-2\fboxrule-1em}%
 \bigskip\begin{lrbox}{\fminibox}\quad\begin{minipage}{\fminilength}\bigskip}
 {\smallskip\end{minipage}\end{lrbox}\noindent\fbox{\usebox{\fminibox}}\bigskip}

\newcommand{\bc}{\begin{fminipage}\color{darkgrey}}
\newcommand{\ec}{\end{fminipage}}

\newcommand{\bp}{\begin{fminipage}\color{lightgrey}}
\newcommand{\ep}{\color{black}\end{fminipage}}

\usepackage{color}
\definecolor{lightgrey}{gray}{0.35}
\definecolor{darkgrey}{gray}{0.20}


\title{Model Checking with HyLoMoC} 

\author{Maja M. D. Jaakson} 

\begin{document}

\maketitle


\section{Introduction}

This paper is a literate Haskell program in which we present an implementation of a hybrid logic--model checker, HyLoMoC, in Haskell.  We begin by introducing the models and hybrid language which are of interest and then show how the implementation proceeds.  The paper concludes with a discussion concerning HyLoMoC's limitations.

\section{Hybrid logics}

Hybrid logics extend modal logics by allowing direct reference to worlds in a model.  A basic hybrid logic typically includes the language of propositional polymodal logic along with a set of \emph{nominals}, which are atomic formulae naming worlds, and a \emph{satisfiability operator} $@_{i}$ for each nominal $i$.  To this basic language of hybrid logic, one may add a converse operator $\Diamond_{i} ^{\smallsmile}$, which makes it possible to speak of what holds at an $i$-predecessor of the current state; an existential or universal operator ${\bf E}$ or ${\bf A}$ (alternatively ${\bf E}x$ or ${\bf A}x$), which allows us to claim a formula holds at some/every state in the model; and the binder operator $\downarrow$, which allows us to bind a world variable to the current state.  In what follows, we deal with a rather rich hybrid logic which contains all of these operators, save the converse operator.  We will use the non-binding ${\bf E}$ as our existential operator. \\

\noindent Let us now give the syntax and semantics of our language, which we shall call $\mathcal{H}(@,{\bf E}, \downarrow)$. \\

\noindent {\bf Definition 2.1} ~~Let ${\sf REL} = \{ \Diamond_{1}, \Diamond_{2}, \Diamond_{3}, \dots \}$ (accessibility relations), ${\sf PROP} = \{ p_{1}, p_{2}, p_{3}, \dots \}$ (proposition letters), ${\sf CONS} = \{ i_{1}, i_{2}, i_{3}, \dots \}$ (constant nominals) and ${\sf VAR} = \{ i_{1}, i_{2}, i_{3}, \dots \}$ (variable nominals) be disjoint and countable sets of symbols.  Well-formed formulae of the hybrid language $\mathcal{H}(@,{\sf E}, \downarrow)$ in the signature ${\sf \langle REL,PROP,CONS,VAR \rangle}$ are defined recursively as follows:
$$ {\sf FORM} ::= p ~|~ i ~|~ x ~|~ \neg \varphi ~|~ \varphi \land \psi ~|~ \Diamond_{j} \varphi ~|~ {\sf E} \varphi ~| \downarrow x . \varphi $$
where $p \in {\sf PROP}$, $i \in {\sf CONS} \cup {\sf VAR}$, $x \in {\sf VAR}$, $\Diamond_{j} \in {\sf REL}$ and $\varphi, \psi \in {\sf FORM}.$ \\

\noindent A hybrid model $\mathbb{M}$ is a quintuple $\mathbb{M} = \langle W, R, V, A, G \rangle$, where $W$ is a non-empty set of worlds or states and $R$ is a subset of ${\sf REL}$ consisting in a set of functions $\Diamond_{j} : W \rightarrow \wp (W)$, which map worlds to their successors.  Note that the valuation function for hybrid logics usually maps members of ${\sf PROP \cup CONS}$ to sets of worlds, with the added condition that the nominals map to singleton sets of worlds; but here, we have split up this function into $V$ and $A$.  The new valuation function $V$ now maps proposition letters to the worlds in which they hold ($V : {\sf PROP} \rightarrow \wp (W)$) and the assignment function $A$ maps each constant nominal to the single world for which it stands ($A : {\sf CONS} \rightarrow W$).  Similarly, $G$ assigns worlds to variable nominals ($G : {\sf VAR} \rightarrow W$).  Given this function, we also define the $x$-variant function $G^{x}_{w}$ as follows: $G^{x}_{w}(y) = w$ when $x = y$; otherwise, $G^{x}_{w}(y) = G(y)$. \\

\noindent We define truth in a pointed model in $\mathcal{H}(@,{\bf E}, \downarrow)$ as follows:
\begin{align*}
\mathbb{M}, G, w & \vDash p & \text{iff  }  & w \in V(p) & \text{ for $p \in {\sf PROP}$} \\
\mathbb{M}, G, w & \vDash i & \text{iff  } & A(i) = w & \text{ for $i \in {\sf CONS}$} \\
\mathbb{M}, G, w & \vDash x & \text{iff  } & G(x) = w & \text{ for $x \in {\sf VAR}$} \\
\mathbb{M}, G, w & \vDash \neg \varphi & \text{iff  } & \mathbb{M}, G, w \nvDash \varphi \\
\mathbb{M}, G, w & \vDash \varphi \land \psi & \text{iff  } & \mathbb{M}, G, w \vDash \varphi \text{ and } \mathbb{M}, G, w \vDash \psi  \\
\mathbb{M}, G, w & \vDash \Diamond_{j} \varphi & \text{iff  } & w' \in \Diamond_{j}(w) \text{ and } \mathbb{M}, G, w' \vDash \varphi & \text{ for some $w' \in {\sf W}$} \\
\mathbb{M}, G, w & \vDash @_{i} \varphi & \text{iff  } & \mathbb{M}, G, A(i) \vDash \varphi & \text{ for $i \in {\sf CONS}$} \\
\mathbb{M}, G, w & \vDash @_{x} \varphi & \text{iff  } & \mathbb{M}, G, G(i) \vDash \varphi & \text{ for $x \in {\sf VAR}$} \\
\mathbb{M}, G, w & \vDash \mathbf{E} \varphi & \text{iff  } & \mathbb{M}, G, w' \vDash \varphi & \text{ for some $w' \in {\sf W}$} \\
\mathbb{M}, G, w & \vDash \downarrow x. \varphi & \text{iff  } & \mathbb{M'}, G^{x}_{w}, w \vDash \varphi & \text{where }\mathbb{M}, \mathbb{M'} \\
& & & & \text{agree on } {\sf W, R, V, A}
\end{align*}

\noindent As usual, one may use $\Box_{j}\varphi$ and ${\bf A}\varphi$ as shorthand for $\neg \Diamond_{j} \neg \varphi$ and $\neg {\bf E} \neg \varphi$ respectively. \\

\noindent So much for the semantics; in the next section, we will show how models of $\mathcal{H}(@,{\bf E}, \downarrow)$ can be represented and how one can implement a model checker for this logic.

\section{HyLoMoC}

Let's begin by importing the two modules we'll be needing, Data.List and Data.Map.  As we shall see later on, Data.Map will be particularly useful for model-building purposes.

\begin{code}
module HyLoMoC where

import Data.List
import Data.Map
\end{code}

\subsection{Language}

We create a \verb^Form^ datatype for our language in a similar style to that used in the Haskell Road project treatment of propositional logic.

\begin{code}
type Name = Int
data Form = Prop Name
          | Cons Name 
          | Var Name        
          | Neg Form
          | Cnj Form Form
          | Dia Int Form
          | At Form Form
          | Exists Form
          | Binder Form Form
          deriving (Eq, Ord)
\end{code}

Thus, in addition to having propositional atoms of the form \verb^Prop x^, we now have constant nominals \verb^Cons x^ and variable nominals \verb^Var x^, where \verb^x^ is a \verb^Name^.  Formulae with the possibility operator as a main connective take an \verb^Int^ $n$ which corresponds to the $n$th member of the set of accessibility relations in a model.  We run into a typing problem with \verb^At^ and \verb^Binder^, however; notice that both of these can take \emph{any} formula as a first argument, while \verb^At^ should only take nominals and \verb^Binder^ should only take variable nominals there.  To get around this, then, we introduce way of checking whether a formula is, indeed, a well-formed formula:

\begin{code}
wff :: Form -> Bool
wff (Prop x)            = True
wff (Cons x)            = True
wff (Var x)             = True
wff (Neg f)             = wff f
wff (Cnj f1 f2)         = wff f1 && wff f2
wff (Dia n f)           = wff f
wff (At (Cons x) f)     = wff f
wff (At (Var x) f)      = wff f
wff (At x f)            = False
wff (Exists f)          = wff f
wff (Binder (Var x) f)  = wff f
wff (Binder x f)        = False
\end{code}

\noindent We can now make our formulae instances of the \verb^Show^ class, using  \verb^!^ to represent $\downarrow$ in binder formulae.

\begin{code}
instance Show Form where 
  show (Prop p)      = "p_" ++ show p
  show (Cons i)      = "i_" ++ show i
  show (Var x)       = "x_" ++ show x
  show (Neg f)       = '~' : show f 
  show (Cnj f1 f2)   = show f1 ++ " & " ++ show f2
  show (Dia n f)     = "<" ++ show n ++ ">" ++ show f
  show (At i f)      = "@_" ++ show i ++
                             " (" ++ show f ++ ")"
  show (Exists f)    = "E (" ++ show f ++ ")"
  show (Binder x f) = "!_" ++ show x ++
                             " (" ++ show f ++ ")"
\end{code}

\noindent Finally, we define \verb^box^ and \verb^forAll^ duals:

\begin{code}
box :: Int -> Form -> Form
box n f = Neg (Dia n  (Neg f))

forAll :: Form -> Form
forAll f = Neg (Exists (Neg f))
\end{code}


\subsection{Models}

We now move on to providing a datatype for our models.

\begin{code}
data Model a = Model { worlds :: [a],
                       rels :: [a -> [a]],
                       val :: Form -> a -> Bool,
                       assn :: Form -> a,
                       g :: Form -> a }
\end{code}

Why do we represent models this way?  For one, $W$ is quite naturally represented as \verb^worlds^, a (possibly infinite) list of \verb^a^s, for instance of type  \verb^Int^ or \verb^String^.  The set of accessibility relations $R$ is represented in an equally natural manner by \verb^rels^, a set of functions from worlds to lists of their successors.  $V$ is cast as \verb^val^, which takes a (\verb^Prop x^) formula and a world and tells us whether the first is true in the latter.  This departs somewhat from the semantics given for $\mathcal{H}(@,{\bf E}, \downarrow)$---which would suggest that \verb^val^ should be of type \verb^[Form -> [a]]^---but the departure is a welcome one: it allows us to use characteristic functions to give valuations on infinite models which would otherwise be less computationally tractable. (More specifically, consider a case in which we want \verb^(Prop x)^ to hold exactly at odd worlds.  If we use a valuation which says \verb^(Prop x)^ holds exactly at each world in [1,3..] and try to check whether \verb^Prop x^ holds at \verb^2^, the checker will never halt; but it will if we use a function which can tell us whether or not \verb^(Prop x)^ is true at any given world.)  Finally, \verb^assn^ assigns a single world to a (\verb^Cons x^) formula; and \verb^g^ assigns a single world to each (\verb^Var x^) formula.

It will be handy to have some models around to use as examples, so we'll give two of them: a finite \verb^babymodel^ and an infinite \verb^infmodel^.  Creating HyLoMoC models is made easier by first defining \verb^functioner^, which takes a list of pairs and a default value as input and outputs a function from the first pair-elements to the second.

\begin{code}
-- mlookup is just shorthand for Data.Map.lookup.
mlookup :: (Ord k) => k -> Map k a -> Maybe a
mlookup = Data.Map.lookup

functioner :: (Ord a) => [(a,b)] -> b -> (a -> b) 
functioner ls defaultvalue = 
                   let listmap = (Data.Map.fromList ls) in
                       (\y -> case (mlookup y listmap) of
                               (Just x) -> x
                               Nothing  -> defaultvalue)
\end{code}

\noindent It's here that the \verb^Data.Map^ module becomes useful.  When we use \verb^functioner^ on a list of pairs \verb^(a,b)^, it first generates a map \verb^listmap^ where the \verb^a^s become keys for the \verb^b^ values.  When the output function is applied to an argument of type \verb^a^, that value is looked up in \verb^listmap^: if it has a return value, the output function gives that value and otherwise, it outputs whatever was chosen as \verb^functioner^'s default value.  Thus, \verb^functioner^ gives us an easy way to generate total functions from lists.

We now have what we need to take a look at our models.  The \verb^babymodel^ has three worlds and a single accessibility relation whereby each world sees every odd world.  \verb^Prop 1^ is true at worlds \verb^1^ and \verb^3^; \verb^Prop 2^ is true at world \verb^2^;  and \verb^Prop 3^ is true at worlds \verb^2^ and \verb^3^.  We use \verb^functioner^ to make \verb^Cons 1^, \verb^2^ and \verb^3^ true at worlds \verb^1^, \verb^2^ and \verb^3^ respectively; all other \verb^Cons x^ are true at world \verb^1^.  We give a similar definition for \verb^g^.

\begin{code}
babymodel = Model [1,2,3]
         [(\y -> [1,3..])] 
         (\y -> case y of 
                 (Prop 1) -> (\w -> elem w [1,3])
                 (Prop 2) -> (\w -> w == 2)
                 (Prop 3) -> (\w -> elem w [2,3])
                 _        -> (\w -> False) )
         (functioner [(Cons 1,1),(Cons 2,2),(Cons 3,3)] 1)
         (functioner [(Var 1,2), (Var 2,1), (Var 3,3)] 1)
\end{code}

\noindent The \verb^infmodel^ has infinitely many worlds.  It too has a single accessibility relation, whereby each world sees (only) its successor.  \verb^Prop 1^ is true exactly at the odd worlds, \verb^Prop 2^ is true exactly at the even ones, and all other \verb^Prop x^ fail to hold at any world.  Each \verb^Cons x^ and \verb^Var x^ maps to its respective world \verb^x^.  (We add error messages for applications of \verb^assn^ and \verb^g^ to non-nominals, but this is not needed for the model checker to run properly.)

\begin{code}
infmodel = Model [1..]
    [(\y -> [y + 1])]
    (functioner [(Prop 1, (\y -> odd y)),
    (Prop 2, (\y -> even y))] (\y -> False))
    (\y -> case y of
           (Cons x) -> x
           _        -> error "Not a cons-nominal." )
    (\y -> case y of
           (Var x) -> x
           _        -> error "Not a var-nominal." )
\end{code}

\subsection{Checkers: isTruein and hyLoMoC}

We are now in a position to see the model checkers themselves.  They come in two flavours: \verb^isTruein^ checks whether a formula holds at a point in a given model, whereas \verb^hyLoMoC^ itself lists the worlds in a model which satisfy the formula provided.  It is, of course, a good idea to run \verb^wff^ on a formula first if one is unsure whether it is well-formed.

\begin{code}
hyLoMoC :: (Ord a) => Model a -> Form -> [a]
hyLoMoC m f = case (worlds m) of
  [] -> error "This model is empty!"
  xs -> Data.List.filter (\y -> isTruein m y f) (worlds m)
\end{code}

\noindent In the event that \verb^hyLoMoC^ is fed a proper model \verb^m^ (i.e., with non-empty \verb^worlds^), it filters the worlds in \verb^m^ of which it's true that \verb^f^ holds in those worlds. In order to do this, \verb^hyLoMoC^ calls \verb^isTruein^, which does most of the actual work.

\begin{code}
isTruein :: (Ord a) => (Model a) -> a -> Form -> Bool
isTruein m w (Prop x)     = val m (Prop x) w
isTruein m w (Cons x)     = assn m (Cons x) == w
isTruein m w (Var x)      = g m (Var x) == w
isTruein m w (Neg f)      = not (isTruein m w f)
isTruein m w (Cnj f1 f2)  = (isTruein m w f1) &&
                            (isTruein m w f2)
isTruein m w (Dia n f)    = any (\y -> isTruein m y f) (((rels m) !! n) w)
isTruein m w (At i f)     = isTruein m (assn m i) f
isTruein m w (Exists f)   = any (\y -> isTruein m y f)
                            (worlds m)
isTruein m w (Binder x f) = isTruein (Model (worlds m) 
                                 (rels m)
                                 (val m)
                                 (assn m)
                                 (\y -> case (x == y) of
                                    True  -> w
                                    False -> g m y)) w f
\end{code}

\noindent Implementing \verb^isTruein^ follows rather straightforwardly from the semantics for $\mathcal{H}(@,{\bf E}, \downarrow)$.  A proposition letter is true at a world in a model iff the valuation function outputs \verb^True^ when given that model, proposition letter, and world.  A constant or variable nominal names a world in a model iff, according to \verb^assn^/\verb^g^, that is the world to which the nominal points.  The negation and conjunction clauses are as usual.  A formula \verb^Dia n f^ holds at a world \verb^w^ in a model \verb^m^ iff there is a \verb^y^ such that \verb^y^ makes \verb^f^ true and \verb^y^ is in the list of worlds accessible to \verb^w^ via the \verb^n^th accessibility relation in \verb^rels m^.  \verb^At i f^ holds at a world in \verb^m^ iff \verb^f^ holds at the world picked out by \verb^assn m i^; and \verb^Exists f^ holds at a world in \verb^m^ iff any world in \verb^worlds m^ satisfies \verb^f^.  Finally, we check whether \verb^Binder x f^ holds at \verb^w^ in \verb^m^ in the manner suggested by our truth definition for $\mathcal{H}(@,{\bf E}, \downarrow)$: we check whether \verb^f^ holds at \verb^w^ in a new model, which agrees on \verb^worlds^, \verb^rels^, \verb^val^ and \verb^assn^ but has a \verb^g^, which is an \verb^x^-variant of \verb^g m^.

We encourage the reader to experiment with \verb^hyLoMoC^, \verb^isTruein^ and our example models.

\subsection{Limitations}

In the preceding, we implemented model checkers for hybrid logic which can tell us, unproblematically, whether a formula is satisfied in a finite pointed model (\verb^isTruein^) and which points in a finite model satisfy that formula (\verb^hyLoMoC^).  Both of these model checkers can deal with infinite models to some extent.  Running \verb^hyLoMoC infmodel (Prop 2)^, for instance, will produce continuous output of even worlds, since \verb^Prop 2^ holds at all even worlds in \verb^infmodel^.  Seeing as \verb^isTruein infmodel w (Exists (Prop 3))^ will never halt nor produce any output for any \verb^w^ (since it continues to go through the list of worlds \verb^[1..]^ looking for a \verb^(Prop 3)^-world), it is not surprising that \verb^hyLoMoC infmodel (Exists (Prop 3))^ will never produce the \verb^[]^ we are looking for.  This is one of the unfortunate limitations we face when it comes to evaluating formulae of hybrid logic on infinite models.\footnote{Thanks to the very helpful Erik Parmann for his advice and suggestions regarding this implementation.}

\end{document}
