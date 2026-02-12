# DOMAIN-SYNTAX v0.1

## 0. Sources & Assumptions

- SRC-SYN001: Enderton, *A Mathematical Introduction to Logic*, 2nd ed., Ch. 1--2 (sentential logic, first-order logic syntax)
- SRC-SYN002: Shoenfield, *Mathematical Logic*, Ch. 2--4 (terms, formulas, formal systems)
- ASM-SYN001: The alphabet of symbols is at most countably infinite. Justification: standard assumption in all classical logic textbooks; ensures the set of formulas is countable, which is essential for Godel numbering (CMP) and Lowenheim-Skolem (CP-004).
- ASM-SYN002: We use parentheses and commas for punctuation and adopt the convention that the outermost connective determines the structure of a formula (unique readability). Justification: SRC-SYN001 (Enderton Ch. 1).
- UNK-SYN001: Resolution of UNK-GLB001 — "connective" is treated as a single primitive (PRIM-SYN003), with individual connectives ($\neg, \to, \land, \lor, \leftrightarrow$) as named instances. Justification: this matches Enderton's treatment and avoids inflating the primitive count. The individual connectives are interdefinable; the primitive notion is "logical connective" as a category. Resolved.

## 1. Domain Intent

- **Irreducible question**: How are well-formed expressions constructed?
- **Scope**: Symbol manipulation prior to any notion of truth or meaning. Formation rules for terms and formulas, structural properties of expressions, substitution operations, and the inductive structure of the formal language.
- **Non-goals**: What expressions mean (SEM). How truths are derived from expressions (DED). Whether syntactic properties are decidable (CMP, though note: "is this string a well-formed formula?" is decidable, but this is a CMP observation about a SYN-defined set).
- **Dissolution argument**: Symbol manipulation is definable without reference to truth, meaning, or computation. Formation rules are purely syntactic — they determine which strings are well-formed without assigning meaning. SYN cannot be merged into SEM because syntax exists prior to and independent of any interpretation: you can study the syntax of a language without ever interpreting it. The set of well-formed formulas is defined by purely combinatorial rules (inductive definition from PRIM-BST014) without reference to structures, truth values, or satisfaction. SYN cannot be merged into DED because deduction involves *sequences* of formulas organized by rules (not just formation of individual formulas).

## 2. Prerequisites

- DEP-SYN001: Requires BST for PRIM-BST001 (set), PRIM-BST009 (function), PRIM-BST010 (finite sequence), PRIM-BST012 (natural number), PRIM-BST013 (mathematical induction), PRIM-BST014 (inductive definition)

## 3. Primitive Notions

- PRIM-SYN001: **Symbol**
  - Description: The basic, indivisible unit from which all expressions are built. Symbols are abstract entities distinguished from one another — we assume we can tell any two distinct symbols apart. The collection of all symbols available for building expressions is called the alphabet.
  - Formal: A symbol is an element of a designated set $\mathcal{A}$ (the alphabet). Symbols include logical symbols (connectives, quantifiers, equality, punctuation) and non-logical symbols (constant, function, and relation symbols).
  - Ownership: OWNS
  - Source: SRC-SYN001 (Enderton Ch. 1), SRC-SYN002 (Shoenfield Ch. 2)
  - Referenced by: SEM (symbols receive interpretation), DED (symbols appear in derivations), CMP (symbols are encoded by Godel numbering)
  - Fragment: both
  - Motivating example: In the language of arithmetic, the symbols include $0$ (constant), $S$ (function symbol for successor), $+$, $\cdot$ (function symbols), $<$ (relation symbol), $=$, $\neg$, $\to$, $\forall$, $($, $)$, and variables $v_0, v_1, v_2, \ldots$.

- PRIM-SYN002: **Variable**
  - Description: A symbol that serves as a placeholder for objects in the domain of discourse. Variables can be free (acting as parameters) or bound (within the scope of a quantifier). We assume a countably infinite supply of variables.
  - Formal: $\text{Var} = \{v_0, v_1, v_2, \ldots\}$, a countably infinite set of distinct symbols. In PL: $\text{PropVar} = \{p_0, p_1, p_2, \ldots\}$ (propositional variables).
  - Ownership: OWNS
  - Source: SRC-SYN001 (Enderton Ch. 2), SRC-SYN002 (Shoenfield Ch. 2)
  - Referenced by: SEM (variable assignment $s : \text{Var} \to |\mathfrak{A}|$), DED (generalization rule, variable restrictions), CMP (Godel numbering of variables)
  - Fragment: both (propositional variables in PL; individual variables in FOL)
  - Motivating example: In $\forall x\, P(x, y)$, $x$ is a bound variable (within scope of $\forall x$) and $y$ is a free variable (a parameter).

- PRIM-SYN003: **Logical Connective**
  - Description: A symbol that combines formulas to form new formulas. The standard connectives are: negation ($\neg$, unary), conditional ($\to$, binary), conjunction ($\land$, binary), disjunction ($\lor$, binary), and biconditional ($\leftrightarrow$, binary). These are interdefinable; a minimal adequate set is $\{\neg, \to\}$ or $\{\neg, \lor\}$.
  - Formal: $\neg$ (arity 1), $\to$ (arity 2), $\land$ (arity 2), $\lor$ (arity 2), $\leftrightarrow$ (arity 2). $(\neg \varphi)$, $(\varphi \to \psi)$, $(\varphi \land \psi)$, $(\varphi \lor \psi)$, $(\varphi \leftrightarrow \psi)$ are formulas whenever $\varphi$ and $\psi$ are formulas.
  - Ownership: OWNS
  - Source: SRC-SYN001 (Enderton Ch. 1), SRC-GLB003 (Mendelson Ch. 1)
  - Referenced by: SEM (truth-functional interpretation of connectives), DED (axiom schemas and rules for each connective)
  - Fragment: both
  - Motivating example: In the formula $(\neg(p \to q) \lor r)$, the outermost connective is $\lor$, which combines $\neg(p \to q)$ and $r$.

- PRIM-SYN004: **Quantifier**
  - Description: A symbol that binds a variable and expresses a claim about all or some objects in the domain. The universal quantifier $\forall$ ("for all") and the existential quantifier $\exists$ ("there exists") are interdefinable: $\exists x\, \varphi \equiv \neg \forall x\, \neg \varphi$.
  - Formal: $\forall x\, \varphi$ and $\exists x\, \varphi$ are formulas whenever $\varphi$ is a formula and $x$ is a variable. The quantifier binds the variable $x$ within its scope $\varphi$.
  - Ownership: OWNS
  - Source: SRC-SYN001 (Enderton Ch. 2), SRC-SYN002 (Shoenfield Ch. 2)
  - Referenced by: SEM (interpretation of quantifiers via structures), DED (quantifier rules: generalization, instantiation)
  - Fragment: FOL (quantifiers are absent from PL)
  - Motivating example: $\forall x\, (P(x) \to Q(x))$ says "for every $x$, if $P(x)$ then $Q(x)$." $\exists x\, P(x)$ says "there is some $x$ such that $P(x)$."

- PRIM-SYN005: **Constant Symbol**
  - Description: A non-logical symbol that names a specific object in the domain of discourse. Unlike variables, constants are not bound by quantifiers and always refer to a fixed (interpretation-dependent) element.
  - Formal: $c, d, c_0, c_1, \ldots$ Constants have arity 0 — they are 0-ary function symbols.
  - Ownership: OWNS
  - Source: SRC-SYN001 (Enderton Ch. 2)
  - Referenced by: SEM (constant symbols receive interpretation as specific domain elements), DED (constants appear in axioms of specific theories)
  - Fragment: FOL
  - Motivating example: In the language of arithmetic, $0$ is a constant symbol naming zero. In a theory of groups, $e$ is a constant symbol naming the identity element.

- PRIM-SYN006: **Function Symbol**
  - Description: A non-logical symbol that represents an operation on domain elements. Each function symbol has a fixed arity $n \geq 1$ indicating the number of arguments it takes.
  - Formal: $f, g, h, \ldots$ with arity $n \in \mathbb{N}$, $n \geq 1$. If $f$ has arity $n$ and $t_1, \ldots, t_n$ are terms, then $f(t_1, \ldots, t_n)$ is a term.
  - Ownership: OWNS
  - Source: SRC-SYN001 (Enderton Ch. 2), SRC-SYN002 (Shoenfield Ch. 2)
  - Referenced by: SEM (function symbols receive interpretation as actual functions on the domain), CMP (function symbols in arithmetic for Godel numbering)
  - Fragment: FOL
  - Motivating example: In the language of arithmetic, $S$ (successor, arity 1), $+$ (addition, arity 2), and $\cdot$ (multiplication, arity 2) are function symbols. The term $S(S(0))$ represents the number 2.

- PRIM-SYN007: **Relation Symbol (Predicate Symbol)**
  - Description: A non-logical symbol that represents a property of or relationship between domain elements. Each relation symbol has a fixed arity $n \geq 1$ indicating the number of arguments. The equality symbol $=$ is a distinguished binary relation symbol that may be included as a logical symbol.
  - Formal: $P, Q, R, \ldots$ with arity $n \in \mathbb{N}$, $n \geq 1$. If $R$ has arity $n$ and $t_1, \ldots, t_n$ are terms, then $R(t_1, \ldots, t_n)$ is an atomic formula.
  - Ownership: OWNS
  - Source: SRC-SYN001 (Enderton Ch. 2), SRC-SYN002 (Shoenfield Ch. 2)
  - Referenced by: SEM (relation symbols receive interpretation as actual relations on the domain), DED (relation symbols appear in axioms of theories)
  - Fragment: FOL (in PL, propositional variables PRIM-SYN002 serve a similar role)
  - Motivating example: In the language of arithmetic, $<$ is a binary relation symbol (arity 2). $<(S(0), S(S(0)))$ (i.e., $1 < 2$) is an atomic formula.

- PRIM-SYN008: **Arity**
  - Description: A natural number $n$ associated with each function symbol or relation symbol, specifying how many arguments it takes. Arity is a function from non-logical symbols to $\mathbb{N}$.
  - Formal: $\text{ar} : \text{FuncSym} \cup \text{RelSym} \to \mathbb{N}$. Constants have arity 0.
  - Ownership: OWNS
  - Source: SRC-SYN001 (Enderton Ch. 2)
  - Referenced by: SEM (interpretation must match arity), DED (rule application respects arity)
  - Fragment: FOL
  - Motivating example: The successor function $S$ has arity 1 (unary). Addition $+$ has arity 2 (binary). The "between" relation $B(x,y,z)$ has arity 3 (ternary).

- PRIM-SYN009: **Language (Signature)**
  - Description: A specification of the non-logical symbols available for building expressions in a particular formal context. A language $\mathcal{L}$ consists of a set of constant symbols, function symbols with arities, and relation symbols with arities. The logical symbols (connectives, quantifiers, variables, parentheses, and optionally $=$) are shared across all languages.
  - Formal: $\mathcal{L} = \langle \mathcal{C}, \mathcal{F}, \mathcal{R}, \text{ar} \rangle$ where $\mathcal{C}$ is a set of constant symbols, $\mathcal{F}$ is a set of function symbols, $\mathcal{R}$ is a set of relation symbols, and $\text{ar}$ assigns arities.
  - Ownership: OWNS
  - Source: SRC-SYN001 (Enderton Ch. 2), SRC-GLB014 (Marker Ch. 1)
  - Referenced by: SEM (structures are $\mathcal{L}$-structures), DED (proofs are in a given language), CMP (decidability is language-relative)
  - Fragment: FOL (in PL, the "language" is simply the set of propositional variables)
  - Motivating example: The language of arithmetic: $\mathcal{L}_{\text{ar}} = \langle \{0\}, \{S, +, \cdot\}, \{<\}, \text{ar} \rangle$ with $\text{ar}(S) = 1$, $\text{ar}(+) = \text{ar}(\cdot) = \text{ar}(<) = 2$. The language of set theory: $\mathcal{L}_\in = \langle \emptyset, \emptyset, \{\in\}, \text{ar} \rangle$ with $\text{ar}(\in) = 2$.

- PRIM-SYN010: **Term**
  - Description: An expression that names or denotes an object. Terms are built inductively from variables and constant symbols using function symbols. Terms are the "noun phrases" of formal languages.
  - Formal: The set of terms $\text{Term}(\mathcal{L})$ is the smallest set such that: (i) every variable $x \in \text{Var}$ is a term; (ii) every constant $c \in \mathcal{C}$ is a term; (iii) if $f \in \mathcal{F}$ has arity $n$ and $t_1, \ldots, t_n$ are terms, then $f(t_1, \ldots, t_n)$ is a term.
  - Ownership: OWNS
  - Source: SRC-SYN001 (Enderton Ch. 2), SRC-SYN002 (Shoenfield Ch. 2)
  - Referenced by: SEM (terms receive interpretation as domain elements), DED (terms appear in substitution instances), CMP (Godel numbering of terms)
  - Fragment: FOL (PL has no terms — propositional variables are atomic)
  - Motivating example: In $\mathcal{L}_{\text{ar}}$: $0$ is a term, $v_0$ is a term, $S(0)$ is a term, $+(S(0), \cdot(v_0, S(S(0))))$ is a term (denoting $1 + x \cdot 2$ in standard notation).

- PRIM-SYN011: **Atomic Formula**
  - Description: The simplest formulas, formed by applying a relation symbol to the appropriate number of terms, or by asserting equality between two terms. Atomic formulas are the "basic sentences" from which all formulas are built.
  - Formal: If $R \in \mathcal{R}$ has arity $n$ and $t_1, \ldots, t_n$ are terms, then $R(t_1, \ldots, t_n)$ is an atomic formula. If $=$ is in the language and $t_1, t_2$ are terms, then $(t_1 = t_2)$ is an atomic formula. In PL: every propositional variable $p \in \text{PropVar}$ is an atomic formula.
  - Ownership: OWNS
  - Source: SRC-SYN001 (Enderton Ch. 2)
  - Referenced by: SEM (base case of satisfaction definition), DED (base case in proof analysis)
  - Fragment: both (propositional variables in PL; relation applications in FOL)
  - Motivating example: $P(a)$, $R(x, f(y))$, $(t_1 = t_2)$ are atomic formulas. In PL, $p$, $q$, $r$ are atomic formulas.

- PRIM-SYN012: **Formula (Well-Formed Formula, wff)**
  - Description: A syntactically correct expression in the formal language, built inductively from atomic formulas using connectives and quantifiers. The set of formulas is the central object of study in syntax — it is the set of "grammatically correct" expressions.
  - Formal: The set of formulas $\text{Form}(\mathcal{L})$ is the smallest set such that: (i) every atomic formula is a formula; (ii) if $\varphi$ is a formula, then $(\neg \varphi)$ is a formula; (iii) if $\varphi, \psi$ are formulas and $\circ \in \{\to, \land, \lor, \leftrightarrow\}$, then $(\varphi \circ \psi)$ is a formula; (iv) [FOL only] if $\varphi$ is a formula and $x$ is a variable, then $(\forall x\, \varphi)$ and $(\exists x\, \varphi)$ are formulas.
  - Ownership: OWNS
  - Source: SRC-SYN001 (Enderton Ch. 1--2), SRC-SYN002 (Shoenfield Ch. 2)
  - Referenced by: SEM (formulas are what get truth values), DED (formulas are what get proved), CMP (set of formulas is decidable)
  - Fragment: both (PL formulas use clauses i--iii; FOL adds clause iv)
  - Motivating example: $(p \to (q \lor r))$ is a PL formula. $(\forall x\, (P(x) \to \exists y\, R(x,y)))$ is an FOL formula. $\forall \to p)($ is NOT a formula.

- PRIM-SYN013: **Sentence (Closed Formula)**
  - Description: A formula with no free variables. Sentences make definite claims — their truth value depends only on the structure, not on a variable assignment.
  - Formal: $\varphi$ is a sentence iff $\text{FV}(\varphi) = \emptyset$, where $\text{FV}(\varphi)$ is the set of free variables of $\varphi$ (see DEF-SYN003).
  - Ownership: OWNS
  - Source: SRC-SYN001 (Enderton Ch. 2)
  - Referenced by: SEM (truth in a structure: $\mathfrak{A} \vDash \varphi$ is defined for sentences), DED (theorems are typically sentences), CMP (theories are sets of sentences)
  - Fragment: FOL (in PL, all formulas are effectively sentences since propositional variables have no internal structure to be "free" or "bound")
  - Motivating example: $\forall x\, (P(x) \to Q(x))$ is a sentence. $P(x) \to Q(x)$ is NOT a sentence — $x$ is free.

- PRIM-SYN014: **Free Occurrence**
  - Description: An occurrence of a variable in a formula that is not within the scope of any quantifier that binds that variable. Free variables act as parameters — the truth of a formula with free variables depends on what values they are assigned.
  - Formal: Defined recursively: (i) In an atomic formula, all variable occurrences are free. (ii) In $(\neg \varphi)$, the free occurrences are those free in $\varphi$. (iii) In $(\varphi \circ \psi)$, the free occurrences are those free in $\varphi$ or free in $\psi$. (iv) In $(\forall x\, \varphi)$ or $(\exists x\, \varphi)$, the free occurrences are those free in $\varphi$ EXCEPT occurrences of $x$.
  - Ownership: OWNS
  - Source: SRC-SYN001 (Enderton Ch. 2)
  - Referenced by: SEM (satisfaction depends on values of free variables), DED (generalization rule restrictions on free variables)
  - Fragment: FOL
  - Motivating example: In $\forall x\,(P(x) \to Q(y))$: the occurrence of $x$ in $P(x)$ is bound; the occurrence of $y$ in $Q(y)$ is free.

- PRIM-SYN015: **Bound Occurrence**
  - Description: An occurrence of a variable within the scope of a quantifier that binds it. Bound variables are placeholders internal to a quantified expression — they can be renamed without changing meaning (alpha-equivalence).
  - Formal: An occurrence of variable $x$ in $\varphi$ is bound iff it is within the scope of a quantifier $\forall x$ or $\exists x$. The quantifier occurrence itself ($\forall x$ or $\exists x$) is also considered a binding occurrence.
  - Ownership: OWNS
  - Source: SRC-SYN001 (Enderton Ch. 2)
  - Referenced by: SEM (bound variables do not affect truth relative to an assignment), DED (renaming bound variables preserves provability)
  - Fragment: FOL
  - Motivating example: In $\forall x\, P(x)$, both occurrences of $x$ (in $\forall x$ and in $P(x)$) are bound. In $P(x) \land \forall x\, Q(x)$, the first $x$ (in $P(x)$) is free and the second (in $Q(x)$) is bound.

- PRIM-SYN016: **Scope**
  - Description: The portion of a formula governed by a particular quantifier or connective. The scope of $\forall x$ in $\forall x\, \varphi$ is $\varphi$. Understanding scope is essential for correctly parsing formulas and determining which variables are free or bound.
  - Formal: In $(\forall x\, \varphi)$, the scope of $\forall x$ is $\varphi$. In $(\varphi \circ \psi)$, the immediate subformulas are $\varphi$ and $\psi$.
  - Ownership: OWNS
  - Source: SRC-SYN001 (Enderton Ch. 2)
  - Referenced by: SEM (scope determines quantifier interpretation), DED (scope determines rule applicability)
  - Fragment: FOL (trivial in PL where there are no quantifiers)
  - Motivating example: In $\forall x\, (P(x) \to \exists y\, Q(x,y))$, the scope of $\forall x$ is $(P(x) \to \exists y\, Q(x,y))$; the scope of $\exists y$ is $Q(x,y)$.

- PRIM-SYN017: **Subformula**
  - Description: A formula that appears as a component within another formula, arising from the inductive construction of that formula. Every formula is a subformula of itself.
  - Formal: Defined recursively: (i) $\varphi$ is a subformula of $\varphi$. (ii) If $(\neg \psi)$ is a subformula of $\varphi$, then $\psi$ is a subformula of $\varphi$. (iii) If $(\psi_1 \circ \psi_2)$ is a subformula of $\varphi$, then $\psi_1$ and $\psi_2$ are subformulas of $\varphi$. (iv) If $(\forall x\, \psi)$ or $(\exists x\, \psi)$ is a subformula of $\varphi$, then $\psi$ is a subformula of $\varphi$.
  - Ownership: OWNS
  - Source: SRC-SYN001 (Enderton Ch. 2)
  - Referenced by: SEM (satisfaction is defined by recursion on subformulas), DED (subformula property in cut-free proofs)
  - Fragment: both
  - Motivating example: The subformulas of $(p \to (q \land r))$ are: $(p \to (q \land r))$, $p$, $(q \land r)$, $q$, $r$.

- PRIM-SYN018: **Equality Symbol ($=$)**
  - Description: A distinguished binary relation symbol, often treated as a logical symbol (part of every language) rather than a non-logical symbol. When $=$ is logical, every language includes atomic formulas of the form $(t_1 = t_2)$, and the equality axioms (reflexivity, symmetry, transitivity, substitution) are logical axioms.
  - Formal: $=$ is a binary relation symbol. $(t_1 = t_2)$ is an atomic formula for any terms $t_1, t_2$. Equality axioms: $\forall x\, (x = x)$; $\forall x\, \forall y\, (x = y \to y = x)$; $\forall x\, \forall y\, \forall z\, (x = y \land y = z \to x = z)$; substitution axiom schemas for function and relation symbols.
  - Ownership: OWNS
  - Source: SRC-SYN001 (Enderton Ch. 2), SRC-SYN002 (Shoenfield Ch. 4)
  - Referenced by: SEM (equality is interpreted as actual identity in normal structures), DED (equality axioms in proof systems)
  - Fragment: FOL
  - Motivating example: $(S(0) = S(0))$ is an atomic formula asserting that the successor of zero equals itself (true in standard arithmetic). $(0 = S(0))$ asserts zero equals the successor of zero (false in standard arithmetic).

## 4. Axioms

- AX-SYN001: **Formation Rules for Terms**
  - Statement: The set $\text{Term}(\mathcal{L})$ is inductively defined (PRIM-BST014) by: (i) every variable is a term; (ii) every constant symbol is a term; (iii) if $f$ has arity $n$ and $t_1, \ldots, t_n$ are terms, then $f(t_1, \ldots, t_n)$ is a term; (iv) nothing else is a term.
  - Depends: PRIM-SYN002 (variable), PRIM-SYN005 (constant), PRIM-SYN006 (function symbol), PRIM-SYN008 (arity), PRIM-SYN010 (term), PRIM-BST014 (inductive definition)
  - Source: SRC-SYN001 (Enderton Ch. 2)
  - Normative: MUST
  - Natural language: Terms are built from the simplest expressions (variables and constants) by applying function symbols. No other way of forming terms is allowed.

- AX-SYN002: **Formation Rules for Formulas**
  - Statement: The set $\text{Form}(\mathcal{L})$ is inductively defined by: (i) every atomic formula is a formula; (ii) if $\varphi$ is a formula, then $(\neg \varphi)$ is a formula; (iii) if $\varphi, \psi$ are formulas and $\circ \in \{\to, \land, \lor, \leftrightarrow\}$, then $(\varphi \circ \psi)$ is a formula; (iv) if $\varphi$ is a formula and $x$ is a variable, then $(\forall x\, \varphi)$ and $(\exists x\, \varphi)$ are formulas; (v) nothing else is a formula.
  - Depends: PRIM-SYN003 (connective), PRIM-SYN004 (quantifier), PRIM-SYN011 (atomic formula), PRIM-SYN012 (formula), PRIM-BST014 (inductive definition)
  - Source: SRC-SYN001 (Enderton Ch. 1--2)
  - Normative: MUST
  - Natural language: Formulas are built from atomic formulas by applying connectives and quantifiers. Every formula has a unique outermost construction step, which is the key to defining operations on formulas by recursion.

- AX-SYN003: **Formation Rules for PL Formulas**
  - Statement: The set $\text{Form}_{\text{PL}}$ is inductively defined by: (i) every propositional variable $p \in \text{PropVar}$ is a formula; (ii) if $\varphi$ is a formula, then $(\neg \varphi)$ is a formula; (iii) if $\varphi, \psi$ are formulas and $\circ \in \{\to, \land, \lor, \leftrightarrow\}$, then $(\varphi \circ \psi)$ is a formula; (iv) nothing else is a formula.
  - Depends: PRIM-SYN002 (variable, propositional), PRIM-SYN003 (connective), PRIM-SYN012 (formula), PRIM-BST014 (inductive definition)
  - Source: SRC-SYN001 (Enderton Ch. 1)
  - Normative: MUST
  - Natural language: Propositional formulas are a restricted fragment of FOL formulas — no terms, no quantifiers, no function or relation symbols. Propositional variables are the atoms.

## 5. Definitions (Conservative Extensions)

- DEF-SYN001: **Substitution ($\varphi[t/x]$)**
  - Definition: The result of replacing every free occurrence of variable $x$ in formula $\varphi$ by term $t$. The substitution is proper (or free for $x$ in $\varphi$) if no variable in $t$ becomes bound after substitution. Defined recursively on the structure of $\varphi$.
  - Formal: $\varphi[t/x]$ defined recursively: (i) If $\varphi$ is atomic, replace each occurrence of $x$ by $t$. (ii) $(\neg \varphi)[t/x] = (\neg \varphi[t/x])$. (iii) $(\varphi \circ \psi)[t/x] = (\varphi[t/x] \circ \psi[t/x])$. (iv) $(\forall y\, \varphi)[t/x] = \forall y\, (\varphi[t/x])$ if $y \neq x$ and $y$ does not occur in $t$; $= \forall y\, \varphi$ if $y = x$. (With appropriate renaming of bound variables to avoid capture.)
  - Depends: PRIM-SYN002 (variable), PRIM-SYN010 (term), PRIM-SYN012 (formula), PRIM-SYN014 (free occurrence), PRIM-SYN015 (bound occurrence)
  - Ownership: OWNS
  - Referenced by: SEM (for variable assignment modification), DED (for rule application, especially universal instantiation)
  - Fragment: FOL (in PL, substitution is trivial — propositional variables have no internal structure)
  - Motivating example: If $\varphi = \forall y\, (P(x) \to Q(x,y))$ and $t = f(y)$, then $\varphi[t/x]$ is NOT proper because $y$ in $t$ would be captured by $\forall y$. After renaming: $\forall z\, (P(f(y)) \to Q(f(y), z))$.

- DEF-SYN002: **Simultaneous Substitution**
  - Definition: The result of simultaneously replacing free occurrences of variables $x_1, \ldots, x_n$ by terms $t_1, \ldots, t_n$ in formula $\varphi$. Simultaneous substitution differs from iterated single substitution when the terms contain variables being substituted.
  - Formal: $\varphi[t_1/x_1, \ldots, t_n/x_n]$. All replacements happen "at once" — a variable introduced by one substitution is not subject to another.
  - Depends: DEF-SYN001 (substitution), PRIM-SYN002 (variable), PRIM-SYN010 (term)
  - Ownership: OWNS
  - Referenced by: SEM (simultaneous assignment modification), DED (multi-variable instantiation)
  - Fragment: FOL
  - Motivating example: $P(x,y)[y/x, x/y] = P(y,x)$ (swap $x$ and $y$). Note: iterated substitution $P(x,y)[y/x][x/y] = P(y,y)[x/y] = P(x,x)$ gives a DIFFERENT result.

- DEF-SYN003: **Free Variables ($\text{FV}(\varphi)$)**
  - Definition: The set of variables that have at least one free occurrence in $\varphi$.
  - Formal: $\text{FV}(\varphi)$ defined recursively: (i) $\text{FV}(R(t_1, \ldots, t_n)) = \text{Var}(t_1) \cup \cdots \cup \text{Var}(t_n)$ where $\text{Var}(t)$ is the set of variables occurring in term $t$. (ii) $\text{FV}(\neg \varphi) = \text{FV}(\varphi)$. (iii) $\text{FV}(\varphi \circ \psi) = \text{FV}(\varphi) \cup \text{FV}(\psi)$. (iv) $\text{FV}(\forall x\, \varphi) = \text{FV}(\varphi) \setminus \{x\}$.
  - Depends: PRIM-SYN002 (variable), PRIM-SYN012 (formula), PRIM-SYN014 (free occurrence)
  - Ownership: OWNS
  - Referenced by: SEM (satisfaction depends on free variables), DED (sentence = formula with $\text{FV} = \emptyset$)
  - Fragment: FOL
  - Motivating example: $\text{FV}(\forall x\,(P(x) \to Q(y))) = \{y\}$. $\text{FV}(P(x) \land Q(x,y)) = \{x, y\}$.

- DEF-SYN004: **Alphabetic Variant (Renaming of Bound Variables)**
  - Definition: Two formulas are alphabetic variants if one can be obtained from the other by consistently renaming bound variables, avoiding capture.
  - Formal: $\varphi$ and $\psi$ are alphabetic variants (written $\varphi \equiv_\alpha \psi$) if they differ only in the names of their bound variables, with each renaming being a consistent bijection that does not introduce variable capture.
  - Depends: PRIM-SYN012 (formula), PRIM-SYN015 (bound occurrence), PRIM-SYN016 (scope)
  - Ownership: OWNS
  - Referenced by: SEM (alphabetic variants have identical semantic behavior), DED (proof systems treat alphabetic variants as interchangeable)
  - Fragment: FOL
  - Motivating example: $\forall x\, P(x)$ and $\forall y\, P(y)$ are alphabetic variants.

- DEF-SYN005: **Structural Induction on Formulas**
  - Definition: A proof technique based on the inductive structure of formulas: to prove a property $P$ holds for all formulas, prove it for atomic formulas (base case), then prove it is preserved by each formula-building operation (connectives, quantifiers).
  - Formal: $[\forall \text{atomic } \varphi\, P(\varphi)] \land [\forall \varphi\, (P(\varphi) \to P(\neg \varphi))] \land [\forall \varphi, \psi\, (P(\varphi) \land P(\psi) \to P(\varphi \circ \psi))] \land [\forall \varphi, x\, (P(\varphi) \to P(\forall x\, \varphi))] \to \forall \varphi\, P(\varphi)$.
  - Depends: PRIM-SYN012 (formula), AX-SYN002 (formation rules), PRIM-BST013 (mathematical induction)
  - Ownership: OWNS
  - Referenced by: SEM (induction on formulas in satisfaction proofs), DED (induction on formula complexity)
  - Fragment: both (PL version omits the quantifier case)
  - Motivating example: Prove every formula has equal numbers of left and right parentheses: base case (atomic formulas have 0); $(\neg \varphi)$ adds 1 of each; $(\varphi \circ \psi)$ adds 1 of each.

- DEF-SYN006: **Structural Recursion on Formulas**
  - Definition: A method of defining a function on formulas by specifying its value for atomic formulas and how it combines values from subformulas at each formula-building step. The unique readability theorem (THM-SYN001) guarantees such definitions are well-defined.
  - Formal: A function $h : \text{Form}(\mathcal{L}) \to X$ is defined by structural recursion by specifying: $h(\text{atomic})$, $h(\neg \varphi) = g_\neg(h(\varphi))$, $h(\varphi \circ \psi) = g_\circ(h(\varphi), h(\psi))$, $h(\forall x\, \varphi) = g_\forall(x, h(\varphi))$.
  - Depends: PRIM-SYN012 (formula), AX-SYN002 (formation rules), PRIM-BST014 (inductive definition), THM-SYN001 (unique readability)
  - Ownership: OWNS
  - Referenced by: SEM (Tarski satisfaction definition is a structural recursion), CMP (Godel numbering can be defined by structural recursion)
  - Fragment: both
  - Motivating example: Defining formula complexity: $\text{cx}(\text{atomic}) = 0$; $\text{cx}(\neg \varphi) = \text{cx}(\varphi) + 1$; $\text{cx}(\varphi \circ \psi) = \max(\text{cx}(\varphi), \text{cx}(\psi)) + 1$; $\text{cx}(\forall x\, \varphi) = \text{cx}(\varphi) + 1$.

- DEF-SYN007: **Formula Complexity (Rank)**
  - Definition: A natural number measuring the nesting depth of connectives and quantifiers in a formula. Defined by structural recursion.
  - Formal: $\text{cx}(\varphi) \in \mathbb{N}$ as in DEF-SYN006 example.
  - Depends: DEF-SYN006 (structural recursion), PRIM-BST012 (natural number)
  - Ownership: OWNS
  - Referenced by: SEM (induction on formula complexity for satisfaction), DED (induction on complexity for metatheorems)
  - Fragment: both
  - Motivating example: $\text{cx}(P(x)) = 0$. $\text{cx}(\neg P(x)) = 1$. $\text{cx}(P(x) \to \forall y\, Q(y)) = 2$.

- DEF-SYN008: **Subterm**
  - Definition: A term that appears as a component within another term, arising from the inductive construction.
  - Formal: Defined recursively: (i) $t$ is a subterm of $t$. (ii) If $f(t_1, \ldots, t_n)$ is a subterm of $s$, then each $t_i$ is a subterm of $s$.
  - Depends: PRIM-SYN010 (term), AX-SYN001 (formation rules for terms)
  - Ownership: OWNS
  - Referenced by: SEM (term evaluation recurs on subterms)
  - Fragment: FOL
  - Motivating example: The subterms of $f(g(a), b)$ are: $f(g(a), b)$, $g(a)$, $a$, $b$.

## 6. Key Theorems

- THM-SYN001: **Unique Readability (for Formulas)**
  - Statement: Every formula can be decomposed into its components in exactly one way. That is, the outermost construction step of any formula is unique: it is either atomic, a negation $(\neg \varphi)$, a binary connective application $(\varphi \circ \psi)$, or a quantification $(\forall x\, \varphi)$ or $(\exists x\, \varphi)$, and the components are uniquely determined.
  - Depends: AX-SYN002 (formation rules), PRIM-SYN012 (formula)
  - Proof sketch: By counting parentheses. The fully parenthesized convention ensures that every proper initial segment of a formula has an excess of left parentheses. This implies that the split point in $(\varphi \circ \psi)$ is unique (SRC-SYN001, Enderton Lemma 1A--1C). Alternatively, by showing the formation rules generate an absolutely free algebra.
  - Source: SRC-SYN001 (Enderton Ch. 1, Theorem 2A)

- THM-SYN002: **Unique Readability (for Terms)**
  - Statement: Every term can be uniquely decomposed: it is either a variable, a constant, or uniquely of the form $f(t_1, \ldots, t_n)$ where $f$, $n$, and $t_1, \ldots, t_n$ are uniquely determined.
  - Depends: AX-SYN001 (formation rules for terms), PRIM-SYN010 (term)
  - Proof sketch: Similar parenthesis-counting argument, or by appeal to the free algebra property.

- THM-SYN003: **Substitution Lemma**
  - Statement: If $t$ is substitutable for $x$ in $\varphi$, and $\mathfrak{A}$ is a structure with assignment $s$, then $\mathfrak{A} \vDash \varphi[t/x][s]$ iff $\mathfrak{A} \vDash \varphi[s(x|t^{\mathfrak{A}}[s])]$. (The semantic effect of substitution matches the effect of changing the variable assignment.)
  - Depends: DEF-SYN001 (substitution), PRIM-SYN010 (term), PRIM-SYN012 (formula). Also references SEM concepts (satisfaction, assignment) but the statement involves SYN operations.
  - Proof sketch: By structural induction on $\varphi$. The key case is the quantifier case, where the "substitutable" condition prevents variable capture. (SRC-SYN001, Enderton Theorem 2A, Ch. 2.)
  - Source: SRC-SYN001 (Enderton Ch. 2)

- THM-SYN004: **Structural Induction/Recursion Principles**
  - Statement: (a) If a property holds for all atomic formulas and is preserved by all formation rules, it holds for all formulas. (b) Any definition by structural recursion on formulas determines a unique function.
  - Depends: AX-SYN002 (formation rules), PRIM-BST013 (mathematical induction), PRIM-BST014 (inductive definition), THM-SYN001 (unique readability)
  - Proof sketch: (a) follows from formulas being inductively defined — they form the smallest set closed under formation rules. (b) follows from unique readability: each formula has a unique decomposition, so recursive clauses never conflict.

## 7. Invariants & Constraints

- INV-SYN001: **Unique Readability**
  - Statement: Every formula in $\text{Form}(\mathcal{L})$ has a unique parse tree (decomposition into subformulas and formation steps).
  - Justification: Without unique readability, structural recursion and structural induction would be ill-defined, and SEM's recursive satisfaction definition would be ambiguous. This invariant is guaranteed by THM-SYN001.

- INV-SYN002: **Countability of Expressions**
  - Statement: For any countable language $\mathcal{L}$ (countably many non-logical symbols), the set of terms $\text{Term}(\mathcal{L})$ and the set of formulas $\text{Form}(\mathcal{L})$ are countable.
  - Justification: Each term/formula is a finite string over a countable alphabet (ASM-SYN001). The set of finite strings over a countable alphabet is countable (THM-BST003). This is essential for Godel numbering (CMP) and Lowenheim-Skolem (CP-004).

- FORBID-SYN001: **No Semantics in Syntax**
  - Statement: SYN definitions and axioms MUST NOT reference truth, satisfaction, models, or semantic consequence. SYN is purely about which strings are well-formed and how they are structured.
  - Consequence: Violation would merge SYN and SEM, destroying the Principle 3 ownership boundary and making the completeness theorem trivial rather than deep.

## 8. Extension Points

- EXT-SYN001: **Modal Operators (Additive)**
  - Fixed: The formation rules pattern (inductive definition of formulas from atoms via connectives).
  - Parameterizable: New unary connectives $\Box$ (necessity) and $\Diamond$ (possibility) are added to the set of logical connectives. Formation rule: if $\varphi$ is a formula, then $\Box \varphi$ and $\Diamond \varphi$ are formulas.
  - Extension type: Additive
  - Examples: Modal logic adds $\Box$/$\Diamond$; temporal logic adds $\mathbf{G}$, $\mathbf{F}$, $\mathbf{U}$.

- EXT-SYN002: **Lambda Abstraction (Additive)**
  - Fixed: The variable and term structure.
  - Parameterizable: New binding operator $\lambda x.\, M$ added. Lambda terms are built from variables, application ($MN$), and abstraction ($\lambda x.\, M$).
  - Extension type: Additive
  - Examples: Lambda calculus as a term language for CMP.

- EXT-SYN003: **Higher-Order Variables (Replacement)**
  - Fixed: The concept of "variable" as a placeholder.
  - Parameterizable: In addition to first-order variables (ranging over objects), add second-order variables (ranging over predicates or functions). This fundamentally changes what "formula" means.
  - Extension type: Replacement
  - Examples: Second-order logic adds predicate variables $X, Y, Z, \ldots$ and allows $\forall X\, \varphi$.

- EXT-SYN004: **Temporal Operators (Additive)**
  - Fixed: The formation rules pattern.
  - Parameterizable: New connectives for temporal modalities: $\mathbf{G}$ (always), $\mathbf{F}$ (eventually), $\mathbf{U}$ (until), $\mathbf{X}$ (next).
  - Extension type: Additive
  - Examples: Linear temporal logic (LTL), computation tree logic (CTL).

## 9. Intra-Domain Dependency Graph

```
PRIM-SYN001 (Symbol)
     |
     +---> PRIM-SYN002 (Variable)
     +---> PRIM-SYN003 (Logical Connective)
     +---> PRIM-SYN004 (Quantifier)
     +---> PRIM-SYN005 (Constant Symbol)
     +---> PRIM-SYN006 (Function Symbol) ---> PRIM-SYN008 (Arity)
     +---> PRIM-SYN007 (Relation Symbol) ---> PRIM-SYN008 (Arity)
     +---> PRIM-SYN018 (Equality Symbol)
     |
     v
PRIM-SYN009 (Language/Signature)
     |
     +---> PRIM-SYN010 (Term) ---> AX-SYN001 (Formation Rules for Terms)
     |                                    |
     |                                    v
     |                              DEF-SYN008 (Subterm)
     |
     +---> PRIM-SYN011 (Atomic Formula)
              |
              v
         PRIM-SYN012 (Formula) ---> AX-SYN002 (Formation Rules)
              |                          |
              +---> PRIM-SYN013 (Sentence)
              +---> PRIM-SYN014 (Free Occurrence)
              +---> PRIM-SYN015 (Bound Occurrence)
              +---> PRIM-SYN016 (Scope)
              +---> PRIM-SYN017 (Subformula)
              |
              v
         DEF-SYN001 (Substitution)
              |
              v
         DEF-SYN002 (Simultaneous Substitution)
         DEF-SYN003 (Free Variables FV)
         DEF-SYN004 (Alphabetic Variant)
         DEF-SYN005 (Structural Induction)
         DEF-SYN006 (Structural Recursion) ---> DEF-SYN007 (Complexity)
```

## 10. Cross-Domain Interface

### Exports

| ID | Concept | Consumed by |
|----|---------|-------------|
| PRIM-SYN001 | Symbol | SEM, DED, CMP |
| PRIM-SYN002 | Variable | SEM, DED, CMP |
| PRIM-SYN003 | Logical Connective | SEM, DED |
| PRIM-SYN004 | Quantifier | SEM, DED |
| PRIM-SYN005 | Constant Symbol | SEM |
| PRIM-SYN006 | Function Symbol | SEM |
| PRIM-SYN007 | Relation Symbol | SEM |
| PRIM-SYN008 | Arity | SEM |
| PRIM-SYN009 | Language (Signature) | SEM, DED, CMP, SET |
| PRIM-SYN010 | Term | SEM, DED |
| PRIM-SYN011 | Atomic Formula | SEM, DED |
| PRIM-SYN012 | Formula (wff) | SEM, DED, CMP |
| PRIM-SYN013 | Sentence | SEM, DED, CMP |
| PRIM-SYN014 | Free Occurrence | SEM, DED |
| PRIM-SYN015 | Bound Occurrence | SEM, DED |
| PRIM-SYN016 | Scope | SEM, DED |
| PRIM-SYN017 | Subformula | SEM, DED |
| PRIM-SYN018 | Equality Symbol | SEM, DED, SET |
| DEF-SYN001 | Substitution | SEM, DED |
| DEF-SYN002 | Simultaneous Substitution | SEM, DED |
| DEF-SYN003 | Free Variables ($\text{FV}$) | SEM, DED |
| DEF-SYN004 | Alphabetic Variant | SEM, DED |
| DEF-SYN005 | Structural Induction | SEM, DED |
| DEF-SYN006 | Structural Recursion | SEM, CMP |
| DEF-SYN007 | Formula Complexity | SEM, DED |
| DEF-SYN008 | Subterm | SEM |

### Imports

| ID | Concept | Provided by |
|----|---------|-------------|
| PRIM-BST001 | Set | BST |
| PRIM-BST009 | Function | BST |
| PRIM-BST010 | Finite Sequence | BST |
| PRIM-BST012 | Natural Number | BST |
| PRIM-BST013 | Mathematical Induction | BST |
| PRIM-BST014 | Inductive Definition | BST |

## 11. Completeness Argument

**Why these primitives cover the domain**: The 18 primitives comprehensively cover the syntactic apparatus needed for classical first-order logic with equality:
- **Lexical level**: symbols (PRIM-SYN001), classified into variables (002), connectives (003), quantifiers (004), constants (005), function symbols (006), relation symbols (007), equality (018), organized by arity (008) into languages (009).
- **Expression level**: terms (010), atomic formulas (011), formulas (012), sentences (013), with structural analysis via subformula (017) and subterm (DEF-SYN008).
- **Variable analysis**: free (014) and bound (015) occurrences, scope (016).
- **Operations**: substitution (DEF-SYN001--002), free variable extraction (DEF-SYN003), alpha-renaming (DEF-SYN004), structural induction/recursion (DEF-SYN005--007).

**Evidence of a gap**: If SEM, DED, or CMP requires a syntactic concept not listed here (e.g., a specific syntactic operation for Godel numbering), it should be added to SYN or shown to be definable from existing SYN entries.

**OL chapters**: `content/first-order-logic/syntax/`, `content/propositional-logic/syntax/`.

## 12. OpenLogic Mapping

| OL Chapter/Section | Maps to |
|---|---|
| `content/first-order-logic/syntax/first-order-languages.tex` | PRIM-SYN001--009 |
| `content/first-order-logic/syntax/terms-formulas.tex` | PRIM-SYN010--012, AX-SYN001, AX-SYN002 |
| `content/first-order-logic/syntax/free-vars-sentences.tex` | PRIM-SYN013--016, DEF-SYN003 |
| `content/first-order-logic/syntax/substitution.tex` | DEF-SYN001, DEF-SYN002 |
| `content/first-order-logic/syntax/unique-readability.tex` | THM-SYN001, THM-SYN002, DEF-SYN005, DEF-SYN006 |
| `content/propositional-logic/syntax/` | PRIM-SYN002 (PL), PRIM-SYN003, PRIM-SYN012 (PL), AX-SYN003 |

## 13. Self-Audit Checklist

- [x] Every PRIM has: description, formal notation, ownership, source, referenced-by, fragment, example
- [x] Every DEF depends only on previously listed PRIM/DEF (check intra-domain graph)
- [x] Every THM depends only on previously listed AX/DEF/THM
- [x] Every cross-domain reference uses full `{Type}-{Code}{Number}` format
- [x] Every import is listed in the source domain's exports
- [x] Dissolution argument is present and non-trivial
- [x] Extension points cover all three types: additive (modal, lambda, temporal), replacement (higher-order)
- [x] Intra-domain dependency graph is acyclic
- [x] Fragment annotations (PL/FOL/both) are present on all PRIM and DEF entries
- [x] Motivating examples are present for all PRIM and key DEF entries
- [x] No PRIM/DEF duplicates an entry in another domain (checked against Primitive Registry)
- [x] Completeness argument addresses all relevant OL chapters
