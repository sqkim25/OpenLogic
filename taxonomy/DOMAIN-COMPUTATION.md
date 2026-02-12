# DOMAIN-COMPUTATION v0.1

## 0. Sources & Assumptions

- SRC-CMP001: Cutland, *Computability*, 1980
- SRC-CMP002: Soare, *Recursively Enumerable Sets and Degrees*, 1987
- SRC-CMP003: Sipser, *Introduction to the Theory of Computation*, 3rd ed., 2012
- ASM-CMP001: We scope computability to "for logic" — only what is needed for metatheorems (undecidability of validity, incompleteness theorems, Church's theorem). Justification: ASM-GLB005.
- ASM-CMP002: We adopt the Church-Turing thesis as a working assumption, identifying the informal notion of "effective procedure" with the formal notion of "Turing-computable function" (equivalently: general recursive function, lambda-definable function). Justification: universal agreement among mathematicians and computer scientists, supported by the equivalence of all proposed formal models (THM-CMP001).
- UNK-CMP001: Where exactly to draw the line between CMP and SET for "arithmetization"? Resolution: Godel numbering is a CMP primitive (PRIM-CMP011) because it is an effective encoding — a computable bijection between expressions and natural numbers. The *existence* of such encodings is a mathematical fact; the *specific encoding scheme* is a CMP design choice. The target domain ($\mathbb{N}$) comes from BST. Resolved.

## 1. Domain Intent

- **Irreducible question**: What is effectively decidable / computable?
- **Scope**: Computable functions, decidable and semi-decidable sets, Turing machines, the Church-Turing thesis, and the undecidability results needed for metatheorems (undecidability of validity, Godel's incompleteness theorems, Tarski's undefinability).
- **Non-goals**: Degrees of unsolvability beyond basic reducibility (no priority arguments, no Turing degrees). Complexity theory (P/NP, polynomial-time reductions). Oracle hierarchies beyond brief mention. Lambda calculus beyond its role as a computation model. Full recursion theory.
- **Dissolution argument**: "Effective procedure" is an **informal, pre-mathematical concept**. The Church-Turing thesis identifies this intuitive notion with formal models (Turing machines, recursive functions, lambda calculus), but this identification is **not itself a theorem** — it is an empirical thesis supported by evidence, not a mathematical proof. This means CMP's core concept cannot be defined in terms of the other domains' formal primitives. CMP cannot be dissolved into SET (Turing machines are set-theoretic constructions, but the *claim* that they capture "all effective procedures" is not set theory). CMP cannot be dissolved into SYN because CMP's primitives inherently involve the concept of **termination and non-termination** — whether a procedure halts on a given input concerns the infinite behavior of a process, which is fundamentally beyond SYN's concern with finite string formation. CMP cannot be dissolved into DED because computability is about functions on $\mathbb{N}$, not about derivability of formulas.

## 2. Prerequisites

- DEP-CMP001: Requires BST for PRIM-BST001 (set), PRIM-BST009 (function), PRIM-BST010 (finite sequence), PRIM-BST012 (natural number), PRIM-BST013 (mathematical induction), PRIM-BST014 (inductive definition), PRIM-BST016 (cardinality)

Note: CMP does NOT directly import from SYN, SEM, or DED. The connections to those domains go through composition patterns (CP-005 through CP-008). Godel numbering (PRIM-CMP011) encodes syntactic objects as numbers, but the encoding is defined within CMP using BST concepts. The syntactic objects being encoded are described informally; formal cross-references to SYN are made in CROSS-DOMAIN-MAP.md.

## 3. Primitive Notions

- PRIM-CMP001: **Computable (Recursive) Function**
  - Description: A function $f : \mathbb{N}^k \to \mathbb{N}$ for which there exists an effective procedure (algorithm) that, given any input $(n_1, \ldots, n_k)$, halts and produces $f(n_1, \ldots, n_k)$. "Computable" is the central concept of this domain. By the Church-Turing thesis (PRIM-CMP005), "computable" is identified with "Turing-computable" and "general recursive."
  - Formal: $f : \mathbb{N}^k \to \mathbb{N}$ is computable (total recursive) iff there exists a Turing machine $M$ such that for all $(n_1, \ldots, n_k) \in \mathbb{N}^k$, $M$ halts on input $(n_1, \ldots, n_k)$ and outputs $f(n_1, \ldots, n_k)$.
  - Ownership: OWNS
  - Source: SRC-CMP001 (Cutland Ch. 1), SRC-GLB007 (Turing 1936)
  - Referenced by: SEM (computable functions in arithmetic), DED (representable functions), SET (computable operations on sets)
  - Fragment: both (in PL: truth-table evaluation is computable)
  - Motivating example: Addition $f(m, n) = m + n$ is computable. The constant-zero function $f(n) = 0$ is computable. Ackermann's function is computable but not primitive recursive.

- PRIM-CMP002: **Primitive Recursive Function**
  - Description: A function built from basic functions (zero, successor, projection) by the operations of composition and primitive recursion. Every primitive recursive function is total and computable, but not every computable function is primitive recursive (Ackermann's function is the standard counterexample).
  - Formal: The class $\mathcal{PR}$ is the smallest class of functions $\mathbb{N}^k \to \mathbb{N}$ containing: (i) zero: $z(n) = 0$; (ii) successor: $s(n) = n+1$; (iii) projections: $p_i^k(n_1, \ldots, n_k) = n_i$; and closed under: (iv) composition: $h(\bar{n}) = f(g_1(\bar{n}), \ldots, g_m(\bar{n}))$; (v) primitive recursion: $h(\bar{n}, 0) = f(\bar{n})$, $h(\bar{n}, m+1) = g(\bar{n}, m, h(\bar{n}, m))$.
  - Ownership: OWNS
  - Source: SRC-CMP001 (Cutland Ch. 2), SRC-GLB008 (Kleene 1952)
  - Referenced by: DED (primitive recursive functions are representable in PA), SET (primitive recursive arithmetic)
  - Fragment: FOL
  - Motivating example: Addition: $\text{add}(m, 0) = m$, $\text{add}(m, n+1) = S(\text{add}(m, n))$. Multiplication: $\text{mult}(m, 0) = 0$, $\text{mult}(m, n+1) = \text{add}(m, \text{mult}(m, n))$.

- PRIM-CMP003: **$\mu$-Recursion (Unbounded Minimization)**
  - Description: The operation that, given a total computable function $f$, produces a new (possibly partial) function $g$ defined by $g(\bar{n}) = $ the least $m$ such that $f(\bar{n}, m) = 0$, if such $m$ exists. This is the operation that takes us beyond primitive recursion to full computability — it introduces the possibility of non-termination (if no such $m$ exists, $g(\bar{n})$ is undefined).
  - Formal: $\mu m[f(\bar{n}, m) = 0] = $ the least $m$ such that $f(\bar{n}, m) = 0$ (undefined if no such $m$ exists). The class of general recursive (= computable) functions is $\mathcal{PR}$ closed under $\mu$-recursion.
  - Ownership: OWNS
  - Source: SRC-CMP001 (Cutland Ch. 4), SRC-GLB008 (Kleene 1952)
  - Referenced by: DED (unbounded search in proof construction)
  - Fragment: FOL
  - Motivating example: Given $f(n, m) = |n - m^2|$ (the absolute difference between $n$ and $m^2$), $\mu m[f(n, m) = 0]$ finds the integer square root of $n$ (if $n$ is a perfect square) or is undefined (if $n$ is not a perfect square).

- PRIM-CMP004: **Turing Machine**
  - Description: A formal model of computation consisting of an infinite tape, a read/write head, a finite set of states, and a transition function. The machine processes input by reading tape symbols, writing symbols, moving the head, and transitioning between states. The Turing machine is one of several equivalent formalizations of "effective procedure."
  - Formal: $M = \langle Q, \Sigma, \Gamma, \delta, q_0, q_{\text{accept}}, q_{\text{reject}} \rangle$ where $Q$ is a finite set of states, $\Sigma$ is the input alphabet, $\Gamma \supseteq \Sigma$ is the tape alphabet (includes blank symbol), $\delta : Q \times \Gamma \to Q \times \Gamma \times \{L, R\}$ is the transition function, $q_0$ is the start state, $q_{\text{accept}}$ and $q_{\text{reject}}$ are halting states.
  - Ownership: OWNS
  - Source: SRC-GLB007 (Turing 1936), SRC-CMP003 (Sipser Ch. 3)
  - Referenced by: SEM (Turing machines as structures), DED (Turing machines formalized in arithmetic)
  - Fragment: FOL
  - Motivating example: A Turing machine that doubles a unary number: reads a string of 1s, appends the same number of 1s. Input $111$ (representing 3) $\to$ output $111111$ (representing 6).

- PRIM-CMP005: **Church-Turing Thesis**
  - Description: The informal thesis (NOT a theorem) that every function that is "effectively computable" (in the intuitive, informal sense) is Turing-computable (equivalently: general recursive, lambda-definable). This identification allows us to use formal computation models as surrogates for the informal concept. Evidence: every proposed computation model (Turing machines, recursive functions, lambda calculus, Post systems, register machines, etc.) computes exactly the same class of functions.
  - Formal: NOT a formal statement. "A function is effectively computable iff it is Turing-computable." This is an empirical thesis, not a mathematical theorem.
  - Ownership: OWNS
  - Source: SRC-GLB006 (Church 1936), SRC-GLB007 (Turing 1936), SRC-CMP001 (Cutland Ch. 6)
  - Referenced by: SEM (informal use in discussing decidability of logical properties), DED (informal appeals in metatheory)
  - Fragment: FOL
  - Motivating example: We say "the set of valid FOL sentences is not decidable" — this uses the Church-Turing thesis to equate the informal "there is no effective decision procedure" with the formal "there is no Turing machine that decides this set."

- PRIM-CMP006: **Decidable Set (Recursive Set, Computable Set)**
  - Description: A set $A \subseteq \mathbb{N}$ for which there exists a computable function that correctly determines membership: given $n$, it always halts and answers "yes" ($n \in A$) or "no" ($n \notin A$).
  - Formal: $A$ is decidable iff its characteristic function $\chi_A : \mathbb{N} \to \{0, 1\}$ (where $\chi_A(n) = 1$ iff $n \in A$) is computable.
  - Ownership: OWNS
  - Source: SRC-CMP001 (Cutland Ch. 5), SRC-CMP003 (Sipser Ch. 4)
  - Referenced by: SEM (decidable theories), DED (decidable proof systems)
  - Fragment: FOL
  - Motivating example: The set of even numbers is decidable (check if $n \bmod 2 = 0$). The set of primes is decidable (trial division). The set of valid PL formulas is decidable (truth tables). The set of valid FOL formulas is NOT decidable (Church's theorem, CP-008).

- PRIM-CMP007: **Semi-Decidable Set (Computably Enumerable, Recursively Enumerable, c.e.)**
  - Description: A set $A \subseteq \mathbb{N}$ for which there exists a computable procedure that accepts every member of $A$ (halts and says "yes") but may run forever on non-members. Equivalently: $A$ is the domain of some partial computable function, or $A$ is empty or the range of some total computable function.
  - Formal: $A$ is semi-decidable (c.e.) iff there exists a partial computable function $f$ such that $A = \text{dom}(f) = \{n : f(n) \text{ is defined}\}$. Equivalently: $A$ is c.e. iff $A = \emptyset$ or $A = \text{range}(g)$ for some total computable $g$.
  - Ownership: OWNS
  - Source: SRC-CMP001 (Cutland Ch. 5), SRC-CMP002 (Soare Ch. 1)
  - Referenced by: DED (the set of theorems of a c.e. theory is c.e.), SEM (satisfiability is c.e.)
  - Fragment: FOL
  - Motivating example: The set of valid FOL sentences is c.e. (enumerate all proofs; for each, record its conclusion). The set of theorems of PA is c.e. The halting set $K = \{e : \varphi_e(e) \text{ halts}\}$ is c.e. but not decidable.

- PRIM-CMP008: **Halting Problem**
  - Description: The problem: given a Turing machine $M$ and input $w$, does $M$ halt on $w$? Turing proved this is undecidable — there is no algorithm that correctly answers this question for all $(M, w)$ pairs. This is the fundamental undecidability result from which most others follow by reduction.
  - Formal: The halting set $K_0 = \{\langle e, n \rangle : \varphi_e(n) \text{ halts}\}$ is c.e. but not decidable. The diagonal halting set $K = \{e : \varphi_e(e) \text{ halts}\}$ is c.e. but not decidable.
  - Ownership: OWNS
  - Source: SRC-GLB007 (Turing 1936), SRC-CMP003 (Sipser Ch. 4)
  - Referenced by: SEM (undecidability of validity reduces from halting), DED (undecidability of provability)
  - Fragment: FOL
  - Motivating example: There is no algorithm that takes a Python program as input and correctly determines whether it terminates on every input. This is the halting problem in a modern guise.

- PRIM-CMP009: **Many-One Reducibility ($\leq_m$)**
  - Description: Set $A$ is many-one reducible to set $B$ (written $A \leq_m B$) if there exists a total computable function $f$ such that $n \in A \iff f(n) \in B$. This formalizes "A is no harder than B" — if you can decide $B$, you can decide $A$ by first computing $f$ and then querying $B$.
  - Formal: $A \leq_m B$ iff there exists a total computable $f : \mathbb{N} \to \mathbb{N}$ such that $\forall n\, (n \in A \iff f(n) \in B)$.
  - Ownership: OWNS
  - Source: SRC-CMP001 (Cutland Ch. 7), SRC-CMP002 (Soare Ch. 3)
  - Referenced by: (internal — used in undecidability proofs)
  - Fragment: FOL
  - Motivating example: To show FOL validity is undecidable, reduce the halting problem to it: given $(e, n)$, effectively construct a sentence $\varphi_{e,n}$ such that $\varphi_{e,n}$ is valid iff machine $e$ halts on input $n$. Then $K_0 \leq_m \text{Val}_{\text{FOL}}$.

- PRIM-CMP010: **Diagonalization**
  - Description: A proof technique that constructs an object that differs from every object in a given enumeration by "diagonalizing" — ensuring it disagrees with the $n$-th object on the $n$-th component. Used in Cantor's theorem, the undecidability of the halting problem, Godel's incompleteness theorem, and Tarski's undefinability theorem.
  - Formal: Given an enumeration $\{f_0, f_1, f_2, \ldots\}$, define $g(n) \neq f_n(n)$ for all $n$. Then $g \neq f_i$ for all $i$.
  - Ownership: OWNS
  - Source: SRC-CMP001 (Cutland Ch. 5), SRC-GLB005 (Godel 1931)
  - Referenced by: SEM (diagonalization in Tarski's theorem), DED (diagonalization in Godel's theorem)
  - Fragment: FOL
  - Motivating example: The halting problem: define $g(e) = $ "halt iff $\varphi_e(e)$ does NOT halt." If $g = \varphi_{e_0}$ for some $e_0$, then $g(e_0)$ halts $\iff$ $\varphi_{e_0}(e_0)$ does NOT halt $\iff$ $g(e_0)$ does NOT halt — contradiction.

- PRIM-CMP011: **Godel Numbering (Arithmetization)**
  - Description: An effective, injective encoding of syntactic objects (symbols, terms, formulas, derivations) as natural numbers. This bridges the syntactic world (SYN/DED) and the arithmetic world (CMP), enabling formal systems to "talk about themselves." Godel numbering is the technical foundation for the incompleteness theorems.
  - Formal: An injective computable function $\ulcorner \cdot \urcorner : \text{Expressions} \to \mathbb{N}$ such that: (i) $\ulcorner \cdot \urcorner$ is computable; (ii) the range is decidable; (iii) basic syntactic operations (substitution, concatenation) correspond to computable (indeed, primitive recursive) operations on the codes.
  - Ownership: OWNS
  - Source: SRC-GLB005 (Godel 1931), SRC-CMP001 (Cutland Ch. 10)
  - Referenced by: SYN (expressions are what gets encoded), DED (derivations are encoded), SEM (truth predicates reference Godel numbers)
  - Fragment: FOL
  - Motivating example: Godel's original encoding: assign a number to each symbol ($\ulcorner ( \urcorner = 1$, $\ulcorner ) \urcorner = 3$, $\ulcorner \neg \urcorner = 5$, etc.), encode a sequence $\langle a_1, \ldots, a_n \rangle$ as $2^{a_1} \cdot 3^{a_2} \cdot 5^{a_3} \cdots p_n^{a_n}$. Then $\ulcorner P(0) \urcorner$ is a specific (large) natural number.

- PRIM-CMP012: **Universal Turing Machine**
  - Description: A single Turing machine $U$ that can simulate any other Turing machine: given an encoding of a machine $M$ and its input $w$, $U$ simulates $M$'s computation on $w$. The existence of a universal machine is the fundamental result enabling self-reference in computation.
  - Formal: There exists a computable function $\varphi_u$ such that $\varphi_u(\langle e, n \rangle) = \varphi_e(n)$ for all $e, n$. Here $e$ is the index (code) of a Turing machine and $\varphi_e$ is the partial function it computes.
  - Ownership: OWNS
  - Source: SRC-GLB007 (Turing 1936), SRC-CMP001 (Cutland Ch. 4)
  - Referenced by: (internal — used in halting problem proof)
  - Fragment: FOL
  - Motivating example: A Python interpreter is a universal Turing machine (for programs written in Python). Given a Python program $P$ and input $x$, the interpreter simulates $P$ on $x$.

## 4. Axioms

CMP has no axioms in the traditional sense. The Church-Turing thesis (PRIM-CMP005) functions as an empirical identification, not a formal axiom. The closure properties of computable functions (composition, primitive recursion, $\mu$-recursion) are theorems, not axioms.

## 5. Definitions (Conservative Extensions)

- DEF-CMP001: **Partial Function**
  - Definition: A function that may be undefined on some inputs. Partial computable functions are the natural output of Turing machines (which may not halt on some inputs).
  - Formal: A partial function $f : \mathbb{N}^k \rightharpoonup \mathbb{N}$. $f(n_1, \ldots, n_k)\downarrow$ means $f$ is defined (halts) at $(n_1, \ldots, n_k)$. $f(n_1, \ldots, n_k)\uparrow$ means undefined (does not halt).
  - Depends: PRIM-BST009 (function), PRIM-CMP001 (computable function)
  - Ownership: OWNS
  - Referenced by: DED (partial functions in proof search), SEM (partial recursive functions)
  - Fragment: FOL
  - Motivating example: The function "search for a proof of $\varphi$ and return its length" is partial — it is undefined when $\varphi$ is not provable.

- DEF-CMP002: **Total Function**
  - Definition: A function defined on all inputs. Every total computable function is computable, but not every computable partial function is total.
  - Formal: $f : \mathbb{N}^k \to \mathbb{N}$ is total iff $f(n_1, \ldots, n_k)\downarrow$ for all $(n_1, \ldots, n_k) \in \mathbb{N}^k$.
  - Depends: DEF-CMP001 (partial function)
  - Ownership: OWNS
  - Referenced by: SEM (total functions in arithmetic structures)
  - Fragment: FOL
  - Motivating example: Addition, multiplication, and exponentiation are total computable functions. The busy beaver function is total but not computable.

- DEF-CMP003: **Characteristic Function ($\chi_A$)**
  - Definition: The function that indicates membership in a set $A$: returns 1 for members, 0 for non-members. A set is decidable iff its characteristic function is computable.
  - Formal: $\chi_A : \mathbb{N} \to \{0, 1\}$ where $\chi_A(n) = 1$ if $n \in A$, $\chi_A(n) = 0$ if $n \notin A$.
  - Depends: PRIM-CMP006 (decidable set), PRIM-BST009 (function)
  - Ownership: OWNS
  - Referenced by: DED (characteristic functions of decidable theories)
  - Fragment: FOL
  - Motivating example: $\chi_{\text{Even}}(n) = 1 - (n \bmod 2)$. $\chi_{\text{Prime}}$ is computable (by trial division).

- DEF-CMP004: **Enumeration (Effective Listing)**
  - Definition: An effective listing of the members of a set: a total computable function $f : \mathbb{N} \to \mathbb{N}$ whose range is the set. A set is c.e. iff it is empty or the range of such an enumeration.
  - Formal: $A = \{f(0), f(1), f(2), \ldots\} = \text{range}(f)$ for a total computable $f$.
  - Depends: PRIM-CMP007 (semi-decidable set), PRIM-CMP001 (computable function)
  - Ownership: OWNS
  - Referenced by: DED (effective enumeration of theorems)
  - Fragment: FOL
  - Motivating example: The set of theorems of PA can be effectively enumerated: systematically generate all derivations of length 1, 2, 3, ... and list their conclusions.

- DEF-CMP005: **Index (Program)**
  - Definition: A natural number $e$ that encodes a Turing machine (or equivalently, a partial recursive function). The function computed by the $e$-th Turing machine is written $\varphi_e$. Every natural number is an index for some partial computable function (some may compute the empty function).
  - Formal: $\varphi_e$ denotes the partial computable function with index $e$. $W_e = \text{dom}(\varphi_e)$ is the $e$-th c.e. set.
  - Depends: PRIM-CMP004 (Turing machine), PRIM-CMP012 (universal machine)
  - Ownership: OWNS
  - Referenced by: (internal — used in halting problem and fixed-point theorem)
  - Fragment: FOL
  - Motivating example: In any standard Godel numbering of Turing machines: $\varphi_7$ is whatever partial function the 7th Turing machine computes. $W_7 = \{n : \varphi_7(n)\downarrow\}$.

- DEF-CMP006: **Lambda-Definable Function**
  - Definition: A function definable in the lambda calculus. By the Church-Turing thesis, the lambda-definable functions are exactly the computable functions. The lambda calculus provides an alternative foundation for computability using function abstraction and application.
  - Formal: A function $f : \mathbb{N} \to \mathbb{N}$ is lambda-definable iff there exists a lambda term $M$ such that for all $n$: $M \bar{n} =_\beta \overline{f(n)}$, where $\bar{n}$ is the Church numeral for $n$.
  - Depends: PRIM-CMP001 (computable function), PRIM-CMP005 (Church-Turing thesis)
  - Ownership: OWNS
  - Referenced by: DED (Curry-Howard correspondence)
  - Fragment: FOL
  - Motivating example: The successor function: $\lambda n. \lambda f. \lambda x. f(n\, f\, x)$ applied to Church numeral $\bar{n} = \lambda f. \lambda x. f^n(x)$ produces $\overline{n+1}$.

- DEF-CMP007: **Productive Set**
  - Definition: A set $A$ such that there exists a computable function $f$ (a "productive function") with the property: for every c.e. set $W_e \subseteq A$, $f(e) \in A \setminus W_e$. Productive sets are "too large" to be c.e. — any attempt to enumerate them computably misses at least one element (constructively).
  - Formal: $A$ is productive via $f$ iff for all $e$: $W_e \subseteq A \Rightarrow f(e) \in A \setminus W_e$.
  - Depends: PRIM-CMP007 (semi-decidable set), PRIM-CMP001 (computable function)
  - Ownership: OWNS
  - Referenced by: (internal — used in showing the complement of the halting set is not c.e.)
  - Fragment: FOL
  - Motivating example: The complement of $K$ (the non-halting set $\bar{K} = \{e : \varphi_e(e)\uparrow\}$) is productive.

- DEF-CMP008: **Creative Set**
  - Definition: A c.e. set whose complement is productive. Creative sets are the "hardest" c.e. sets (in fact, they are all $m$-equivalent to $K$).
  - Formal: $A$ is creative iff $A$ is c.e. and $\bar{A}$ is productive.
  - Depends: PRIM-CMP007 (semi-decidable set), DEF-CMP007 (productive set)
  - Ownership: OWNS
  - Referenced by: (internal — classification of c.e. sets)
  - Fragment: FOL
  - Motivating example: The halting set $K$ is creative: it is c.e., and its complement $\bar{K}$ is productive (given any $W_e \subseteq \bar{K}$, the index $e$ itself witnesses $e \in \bar{K} \setminus W_e$, since if $e \in W_e$ then $e \in \bar{K}$ means $\varphi_e(e)\uparrow$, contradicting $e \in W_e \subseteq \bar{K}$... actually the productive function is the identity $f(e) = e$).

- DEF-CMP009: **Representability (in a Formal Theory)**
  - Definition: A function $f : \mathbb{N}^k \to \mathbb{N}$ is representable in a theory $T$ if there exists a formula $\varphi(x_1, \ldots, x_k, y)$ such that for all $n_1, \ldots, n_k, m \in \mathbb{N}$: $f(n_1, \ldots, n_k) = m$ iff $T \vdash \varphi(\bar{n}_1, \ldots, \bar{n}_k, \bar{m})$, where $\bar{n}$ is the numeral for $n$. A set $A \subseteq \mathbb{N}$ is representable if its characteristic function is representable.
  - Formal: $f$ is representable in $T$ via $\varphi(x_1, \ldots, x_k, y)$ iff for all $\bar{n}, m$: $f(\bar{n}) = m \Rightarrow T \vdash \varphi(\bar{n}, \bar{m})$ and $f(\bar{n}) = m \Rightarrow T \vdash \forall y\, (\varphi(\bar{n}, y) \to y = \bar{m})$.
  - Depends: PRIM-CMP001 (computable function), PRIM-CMP011 (Godel numbering). Cross-references: PRIM-DED006 (provability), PRIM-SYN012 (formula).
  - Ownership: OWNS (the concept of representability is about the computability-theoretic relationship between functions and formal theories — Boundary: P3)
  - Referenced by: DED (representability of recursive functions in PA is key to incompleteness), SEM (representable functions are definable in arithmetic)
  - Fragment: FOL
  - Motivating example: Addition is representable in PA via the formula $\varphi(x, y, z) \equiv (x + y = z)$. For instance, $PA \vdash (SS0 + SSS0 = SSSSS0)$ (i.e., $2 + 3 = 5$).

- DEF-CMP010: **Recursive Enumerability (Equivalent Characterizations)**
  - Definition: A set $A \subseteq \mathbb{N}$ satisfies any (and hence all) of these equivalent conditions: (i) $A$ is the domain of a partial computable function; (ii) $A$ is empty or the range of a total computable function; (iii) $A$ is the range of a partial computable function; (iv) $A = \{n : \exists m\, R(n, m)\}$ for a decidable (primitive recursive) relation $R$.
  - Formal: $A$ is c.e. iff $A = \text{dom}(\varphi_e)$ for some $e$ iff ($A = \emptyset$ or $A = \text{range}(f)$ for total computable $f$) iff $A = \{n : \exists m\, R(n, m)\}$ for decidable $R$.
  - Depends: PRIM-CMP007 (semi-decidable set), PRIM-CMP006 (decidable set), DEF-CMP001 (partial function)
  - Ownership: OWNS
  - Referenced by: DED (c.e. characterization of theorem sets)
  - Fragment: FOL
  - Motivating example: The set of theorems of PA is c.e. (enumerate all proofs, collect conclusions). By characterization (iv): $\varphi \in \text{Thm}(PA)$ iff $\exists d$ ($d$ is a proof of $\varphi$ in PA), where "is a proof of" is a primitive recursive relation.

## 6. Key Theorems

- THM-CMP001: **Equivalence of Computation Models**
  - Statement: The following define the same class of functions: (a) Turing-computable functions, (b) general recursive functions ($\mathcal{PR}$ + $\mu$-recursion), (c) lambda-definable functions. Also equivalent: register machines, Post systems, Markov algorithms, etc.
  - Depends: PRIM-CMP001, PRIM-CMP002, PRIM-CMP003, PRIM-CMP004, DEF-CMP006
  - Proof sketch: Turing $\to$ recursive: simulate Turing machine computation using recursive functions. Recursive $\to$ lambda: encode numbers as Church numerals, encode recursion via fixed-point combinators. Lambda $\to$ Turing: build a Turing machine that reduces lambda terms.
  - Source: SRC-CMP001 (Cutland Ch. 6)

- THM-CMP002: **Unsolvability of the Halting Problem**
  - Statement: The halting set $K = \{e : \varphi_e(e)\downarrow\}$ is not decidable.
  - Depends: PRIM-CMP008 (halting problem), PRIM-CMP006 (decidable set), PRIM-CMP010 (diagonalization)
  - Proof sketch: Suppose $K$ is decidable via total computable $f$. Define $g(e) = $ "if $f(e) = 1$ (i.e., $e \in K$) then loop forever; else halt." $g$ is partial computable; let $e_0$ be its index. $e_0 \in K \iff \varphi_{e_0}(e_0)\downarrow \iff g(e_0)\downarrow \iff e_0 \notin K$. Contradiction.
  - Source: SRC-GLB007 (Turing 1936)

- THM-CMP003: **Rice's Theorem**
  - Statement: Every non-trivial extensional property of c.e. sets (i.e., every property that depends only on which function $\varphi_e$ computes, not on the index $e$ itself) is undecidable.
  - Depends: PRIM-CMP006 (decidable), DEF-CMP005 (index), THM-CMP002 (halting unsolvability)
  - Proof sketch: Reduce the halting problem to any non-trivial property. If the property $P$ is non-trivial, then there exist indices $a, b$ with $\varphi_a \in P$ and $\varphi_b \notin P$. Use the $s$-$m$-$n$ theorem to construct a reduction.
  - Source: SRC-CMP001 (Cutland Ch. 7)

- THM-CMP004: **$s$-$m$-$n$ Theorem (Parameter Theorem)**
  - Statement: There exists a total computable injective function $s_n^m$ such that $\varphi_{s_n^m(e, x_1, \ldots, x_m)}(y_1, \ldots, y_n) = \varphi_e(x_1, \ldots, x_m, y_1, \ldots, y_n)$.
  - Depends: DEF-CMP005 (index), PRIM-CMP001 (computable function)
  - Proof sketch: Given an index $e$ and parameters $x_1, \ldots, x_m$, effectively construct a new index that "hardcodes" these parameters. This is a basic property of any reasonable indexing of computable functions.
  - Source: SRC-CMP001 (Cutland Ch. 4), SRC-GLB008 (Kleene 1952)

- THM-CMP005: **Recursion Theorem (Fixed-Point Theorem, Kleene)**
  - Statement: For every total computable function $f$, there exists an index $e$ such that $\varphi_e = \varphi_{f(e)}$. Informally: every computable transformation of programs has a fixed point.
  - Depends: DEF-CMP005 (index), THM-CMP004 ($s$-$m$-$n$)
  - Proof sketch: Define $d(x, y) = \varphi_{f(s(x,x))}(y)$ where $s$ is from the $s$-$m$-$n$ theorem. Let $n$ be an index for $d$. Then $e = s(n,n)$ is the fixed point: $\varphi_e(y) = \varphi_{s(n,n)}(y) = d(n,y) = \varphi_{f(s(n,n))}(y) = \varphi_{f(e)}(y)$.
  - Source: SRC-CMP001 (Cutland Ch. 11)

## 7. Invariants & Constraints

- INV-CMP001: **Church-Turing Robustness**
  - Statement: Every proposed formal model of computation (past and future) computes exactly the same class of functions as Turing machines.
  - Justification: Empirical — confirmed by all known computation models. This invariant is the basis for the Church-Turing thesis (PRIM-CMP005). Not a formal theorem but an observed regularity.

- INV-CMP002: **Closure Properties**
  - Statement: The class of decidable sets is closed under complement, union, intersection. The class of c.e. sets is closed under union, intersection but NOT complement. A set is decidable iff both it and its complement are c.e.
  - Justification: Standard theorems of computability theory.

- FORBID-CMP001: **Church-Turing Thesis is NOT a Theorem**
  - Statement: No domain spec or composition pattern may cite the Church-Turing thesis as a formal axiom or theorem. It is always an informal identification.
  - Consequence: Arguments that rely on the Church-Turing thesis must be flagged as depending on an empirical thesis, not a mathematical proof.

## 8. Extension Points

- EXT-CMP001: **Oracle Computation and Arithmetical Hierarchy (Additive)**
  - Fixed: Computable functions, decidable sets, c.e. sets.
  - Parameterizable: Relativized computation: Turing machines with an "oracle" for a set $A$ (can query "$n \in A$?" in one step). The arithmetical hierarchy ($\Sigma_n^0$, $\Pi_n^0$) classifies sets by the number of quantifier alternations needed.
  - Extension type: Additive
  - Examples: $\Sigma_1^0 = $ c.e. $\Sigma_2^0 = $ limits of c.e. sets. Post's theorem connects the hierarchy to oracle computation.

- EXT-CMP002: **Complexity Classes (Additive)**
  - Fixed: Decidable sets.
  - Parameterizable: Restrict computation by resource bounds (time, space). P (polynomial time), NP (non-deterministic polynomial time), PSPACE, etc.
  - Extension type: Additive
  - Examples: SAT is NP-complete. TAUT is coNP-complete. Validity of PL formulas is coNP-complete.

## 9. Intra-Domain Dependency Graph

```
PRIM-CMP002 (Primitive Recursive)
     |
     v
PRIM-CMP003 (mu-Recursion)
     |
     v
PRIM-CMP001 (Computable Function)
     |
     +---> PRIM-CMP004 (Turing Machine)
     |          |
     |          v
     |     PRIM-CMP012 (Universal TM)
     |          |
     |          v
     |     DEF-CMP005 (Index/Program)
     |
     +---> PRIM-CMP005 (Church-Turing Thesis)
     +---> PRIM-CMP006 (Decidable Set) --> DEF-CMP003 (Characteristic Function)
     +---> PRIM-CMP007 (Semi-Decidable) --> DEF-CMP004 (Enumeration)
     |          |                           DEF-CMP010 (Equiv. Characterizations)
     |          +---> DEF-CMP007 (Productive Set)
     |          +---> DEF-CMP008 (Creative Set)
     |
     +---> PRIM-CMP008 (Halting Problem) [depends: CMP006, CMP010]
     +---> PRIM-CMP009 (Many-One Reducibility)
     +---> PRIM-CMP010 (Diagonalization)
     +---> PRIM-CMP011 (Godel Numbering)
     |
     +---> DEF-CMP001 (Partial Function)
     +---> DEF-CMP002 (Total Function)
     +---> DEF-CMP006 (Lambda-Definable)
     +---> DEF-CMP009 (Representability)
```

## 10. Cross-Domain Interface

### Exports

| ID | Concept | Consumed by |
|----|---------|-------------|
| PRIM-CMP001 | Computable Function | SEM, DED, SET |
| PRIM-CMP002 | Primitive Recursive Function | DED, SET |
| PRIM-CMP004 | Turing Machine | SEM, DED |
| PRIM-CMP005 | Church-Turing Thesis | SEM, DED |
| PRIM-CMP006 | Decidable Set | SEM, DED |
| PRIM-CMP007 | Semi-Decidable Set | DED |
| PRIM-CMP008 | Halting Problem | SEM, DED |
| PRIM-CMP009 | Many-One Reducibility | SEM |
| PRIM-CMP010 | Diagonalization | SEM, DED |
| PRIM-CMP011 | Godel Numbering | SYN, DED, SEM |
| PRIM-CMP012 | Universal Turing Machine | DED |
| DEF-CMP001 | Partial Function | DED, SEM |
| DEF-CMP002 | Total Function | SEM |
| DEF-CMP005 | Index (Program) | DED |
| DEF-CMP009 | Representability | DED, SEM |
| DEF-CMP010 | Recursive Enumerability (equiv. char.) | DED |

### Imports

| ID | Concept | Provided by |
|----|---------|-------------|
| PRIM-BST001 | Set | BST |
| PRIM-BST009 | Function | BST |
| PRIM-BST010 | Finite Sequence | BST |
| PRIM-BST012 | Natural Number | BST |
| PRIM-BST013 | Mathematical Induction | BST |
| PRIM-BST014 | Inductive Definition | BST |
| PRIM-BST016 | Cardinality | BST |

## 11. Completeness Argument

**Why these primitives cover the domain**: The 12 primitives + 10 definitions cover computability theory as needed for logic metatheorems:
- **Core computability**: computable functions (001), primitive recursive (002), $\mu$-recursion (003), Turing machines (004), Church-Turing thesis (005), universal TM (012).
- **Decidability spectrum**: decidable sets (006), semi-decidable sets (007), halting problem (008).
- **Proof techniques**: many-one reducibility (009), diagonalization (010).
- **Logic bridge**: Godel numbering (011), representability (DEF-009).
- **Function types**: partial/total (DEF-001/002), characteristic (DEF-003), lambda-definable (DEF-006).
- **Set classification**: enumeration (DEF-004), productive/creative (DEF-007/008), c.e. equivalences (DEF-010).

**Scope check**: per ASM-CMP001, we include only what's needed for metatheorems. CP-005 (Godel I) needs: PRIM-CMP011 (Godel numbering), PRIM-CMP010 (diagonalization), DEF-CMP009 (representability). CP-008 (Church undecidability) needs: PRIM-CMP008 (halting), PRIM-CMP009 (reducibility), PRIM-CMP006 (decidable). All present.

**OL chapters**: `content/computability/`, `content/turing-machines/`, `content/lambda-calculus/`.

## 12. OpenLogic Mapping

| OL Chapter/Section | Maps to |
|---|---|
| `content/computability/recursive-functions/` | PRIM-CMP001--003, DEF-CMP001--003 |
| `content/turing-machines/` | PRIM-CMP004, PRIM-CMP012, DEF-CMP005 |
| `content/computability/computably-enumerable-sets/` | PRIM-CMP007, DEF-CMP004, DEF-CMP007, DEF-CMP008, DEF-CMP010 |
| `content/computability/halting-problem/` | PRIM-CMP008, PRIM-CMP010 |
| `content/computability/reducibility-degrees/` | PRIM-CMP009 |
| `content/incompleteness/arithmetization-syntax/` | PRIM-CMP011 |
| `content/incompleteness/representability-in-q/` | DEF-CMP009 |
| `content/lambda-calculus/` | DEF-CMP006 |

## 13. Self-Audit Checklist

- [x] Every PRIM has: description, formal notation, ownership, source, referenced-by, fragment, example
- [x] Every DEF depends only on previously listed PRIM/DEF (check intra-domain graph)
- [x] Every THM depends only on previously listed AX/DEF/THM
- [x] Every cross-domain reference uses full `{Type}-{Code}{Number}` format
- [x] Every import is listed in the source domain's exports
- [x] Dissolution argument is present and non-trivial
- [x] Extension points cover applicable types (additive for CMP; replacement/structural N/A for computability)
- [x] Intra-domain dependency graph is acyclic
- [x] Fragment annotations (PL/FOL/both) are present on all PRIM and DEF entries
- [x] Motivating examples are present for all PRIM and key DEF entries
- [x] No PRIM/DEF duplicates an entry in another domain (checked against Primitive Registry)
- [x] Completeness argument addresses all relevant OL chapters
