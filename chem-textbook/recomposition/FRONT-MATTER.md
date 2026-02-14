# Front Matter

---

## Preface

This is not a typical chemistry textbook. Most introductory chemistry courses ask you to memorize a large number of facts --- names of elements, rules for balancing equations, definitions you reproduce on exams and then forget. This book takes a different approach. Instead of asking *what do you need to remember?*, it asks *how do you need to think?*

The core idea is simple. Chemistry, like any science, rests on a surprisingly small set of **reasoning moves** --- portable cognitive tools that let you figure things out rather than look them up. When a doctor reads a drug interaction warning, when an environmental scientist evaluates a pollution claim, when you decide whether a cleaning product is safe to mix with another one, the underlying reasoning is the same: a handful of moves about composition, structure, energy, and change, applied in combination. This book teaches you those moves explicitly, so you can use them long after the course is over.

We have organized the material around **five question-driven domains**, each corresponding to a chapter, plus an optional sixth capstone:

1. **What is stuff made of?** (Composition)
2. **How is it put together?** (Structure)
3. **What drives change?** (Energy)
4. **How much? How big?** (Scale)
5. **What happens?** (Change)
6. **Chemistry meets life** (an optional capstone that applies the same primitives to DNA, proteins, and biochemistry)

Each chapter introduces between 10 and 15 reasoning moves, grounded in everyday examples --- tap water, cooking, breathing, batteries, medication. You will learn, for instance, that "given a molecular formula, count atoms of each element to determine the formula's composition" is a reasoning move, and that it composes naturally with moves from other domains to explain why ice floats, why vinegar reacts with baking soda, or why carbon dioxide traps heat.

The mathematical ceiling is intentionally low. You will need proportional reasoning (if one mole weighs this much, how much do two moles weigh?), basic algebra (solve for an unknown in a simple equation), and a brief encounter with logarithms when we discuss pH. That is all. No calculus, no advanced math, no assumed fluency with scientific notation beyond what you encountered in high school.

No prior chemistry is required beyond what you saw in a general high school science course. If you remember that water is H₂O and that the periodic table exists, you have enough background to begin.

A note on how this book was developed. The reasoning moves, their dependencies, and their composition patterns were built using a systematic taxonomy approach inspired by formal methods in logic and computer science. Every primitive was catalogued, every dependency was traced, and every cross-domain pattern was verified for completeness before a single chapter was drafted. The result is a textbook where nothing is introduced without a clear reason, nothing is redundant, and every concept connects to something you already know.

Welcome to chemistry as a way of thinking.

---

## Your Chemical Toolkit

### The Five Domains (Plus One)

Chemistry is vast, but the questions it answers are not. This book is organized around five governing questions. Each question defines a domain, and each domain teaches you a set of reasoning moves --- the cognitive tools you will use throughout the course and beyond.

| Chapter | Domain | Governing Question | What You'll Learn |
|---------|--------|-------------------|-------------------|
| 1 | Composition (COM) | What is stuff made of? | 13 reasoning moves for identifying atoms, elements, compounds, and formulas |
| 2 | Structure (STR) | How is it put together? | 15 reasoning moves for bonds, molecular shapes, polarity, and intermolecular forces |
| 3 | Energy (NRG) | What drives change? | 11 reasoning moves for energy transfer, entropy, spontaneity, and activation energy |
| 4 | Scale (SCL) | How much? How big? | 11 reasoning moves for moles, concentration, and proportional reasoning |
| 5 | Change (CHG) | What happens? | 12 reasoning moves for chemical equations, equilibrium, rate, acids and bases, and redox |
| 6 | Life (MULTI) | Chemistry meets life | Optional capstone: the same primitives explain DNA, proteins, and metabolism |

Together, these 62 reasoning moves (plus the capstone applications) form your **chemical toolkit**. Once you have them, you can reason through situations you have never seen before --- not because you memorized the answer, but because you own the moves.

### How the Domains Build on Each Other

The domains are not independent. They form a dependency chain, and the book is sequenced to respect it:

```
COM (What is stuff made of?)
 |-- STR (How is it put together?)
 |    \-- (used by NRG, SCL, CHG, MULTI)
 |-- NRG (What drives change?)
 |    \-- (used by CHG)
 |-- SCL (How much? How big?)
 |    \-- (used by CHG, MULTI)
 \-- CHG (What happens?)
      \-- MULTI (Chemistry meets life) [optional]
```

**Composition (COM)** is the foundation. Everything starts with knowing what stuff is made of --- atoms, elements, compounds, and how we represent them. You cannot discuss structure without knowing what you are structuring.

**Structure (STR)** and **Energy (NRG)** both build directly on Composition. Structure asks how atoms connect and arrange themselves. Energy asks what drives those arrangements to form or break apart. These two domains are largely independent of each other and could, in principle, be read in either order --- but we place Structure first because several Energy reasoning moves reference molecular shape.

**Scale (SCL)** builds on Composition and Structure. Once you know what something is made of and how it is put together, you can ask *how much* --- how many atoms, what concentration, what mass. Scale is where proportional reasoning enters the picture.

**Change (CHG)** builds on everything that came before. Chemical change involves composition (what reacts?), structure (why does it react?), energy (is the reaction favorable?), and scale (how much product forms?). This is the domain where your reasoning moves combine most powerfully.

**Life (MULTI)** is the optional capstone. It introduces no new primitives. Instead, it shows that the same 62 reasoning moves you already own are sufficient to explain the chemistry of DNA, protein folding, enzyme catalysis, and metabolism. If your course includes a biochemistry unit, this chapter demonstrates the payoff of the reasoning-move approach: you do not need a separate set of rules for biological chemistry.

### Composition Patterns: Where Domains Meet

At the end of several chapters, you will encounter **Composition Pattern (CP) capstone sections**. These are extended worked examples that weave together reasoning moves from multiple domains into a single explanatory chain. They show you that chemistry's real power lies not in individual moves but in their combination.

There are seven Composition Patterns distributed across the book:

| Pattern | Title | Location | Domains Combined |
|---------|-------|----------|-----------------|
| CP-001 | Structure-to-Property Prediction | End of Chapter 4 | COM + STR + SCL |
| CP-002 | Energy-Driven Transformation | End of Chapter 5 | COM + STR + NRG + CHG |
| CP-003 | Acid-Base in the Body | End of Chapter 5 | COM + SCL + CHG |
| CP-004 | Greenhouse Effect | End of Chapter 4 | COM + STR + NRG + SCL |
| CP-005 | Dose Makes the Poison | End of Chapter 5 | COM + SCL + CHG |
| CP-006 | Food Chemistry | End of Chapter 5 | COM + NRG + SCL + CHG |
| CP-007 | Biochemistry Connection | Chapter 6 | All domains |

For example, CP-004 (Greenhouse Effect) chains together reasoning moves about molecular composition (what is CO₂?), molecular shape and polarity (why does it absorb infrared light?), energy transfer (what happens to that absorbed energy?), and scale (what does 420 ppm mean for the atmosphere?). No single domain can explain the greenhouse effect alone. The Composition Pattern shows you how the moves interlock.

Think of these patterns as the "boss levels" of each chapter --- the places where you see your toolkit working at full capacity.

---

## Notation Guide

Chemistry has its own shorthand. This book uses a minimal, consistent set of conventions so that notation never becomes a barrier to understanding. Every symbol is explained on first use in every chapter, but the table below serves as a quick reference.

| Category | Convention | Example |
|----------|-----------|---------|
| Formula representation | Molecular formulas throughout | H₂O, CO₂, C₃H₈ |
| Charge notation | Superscript after the element or group | Na⁺, Cl⁻ |
| Energy units | kJ for thermochemistry; Calories for food and nutrition | ΔH = -890 kJ; 200 Calories per serving |
| Enthalpy notation | ΔH with no subscripts unless comparing multiple values | ΔH < 0 means exothermic (releases heat) |
| Concentration | "concentration" in prose; M (molar) in equations | 0.1 M NaCl |
| Trace quantities | ppm (parts per million) | 0.7 ppm fluoride in tap water |
| Temperature | °C for everyday contexts; K (kelvin) only when a formula requires it | Water boils at 100 °C |
| Electron representation | Dots for lone pairs; lines for bonds | H--O--H |
| Reaction arrows | → for reactions that go to completion; ⇌ for equilibrium | N₂ + 3H₂ ⇌ 2NH₃ |
| Element symbols | Standard IUPAC symbols; full name on first use per chapter | Sodium (Na) |

A few additional notes:

- **Subscripts and superscripts** appear as formatted text (H₂O, Na⁺) rather than as typed-out approximations. If you are reading a plain-text version of this book, subscripts are written after an underscore (H_2O) and superscripts after a caret (Na^+).
- **Units always follow a number with a space**: 100 °C, not 100°C; 2.5 kJ, not 2.5kJ.
- **We prefer everyday language over jargon**: "concentration" rather than "molarity" in running prose, "heat released" rather than "exothermic enthalpy change" until the technical term has been properly introduced.

---

## How to Read This Book

Each chapter follows a consistent structure built around the reasoning moves. Here is what to expect as you read.

**Reasoning Move Blockquotes.** Every new reasoning move is introduced in a blockquote with a standard format: *Given X, do Y to determine Z.* For example:

> **COM-04: Formula Interpretation.** Given a molecular formula, count the subscript after each element symbol to determine how many atoms of that element are present in one unit of the substance.

These blockquotes are your primary reference. When you encounter one, slow down --- this is a new tool entering your toolkit.

**Dependency Annotations.** When a reasoning move relies on an earlier one, you will see an italic note like *[Recall COM-04: Formula Interpretation]*. These annotations tell you exactly which prior tool is being recalled. If the reference feels unfamiliar, flip back and review it before continuing. The annotations also serve as a self-diagnostic: if you consistently need to look up a particular move, it is worth spending extra time on it.

**Reasoning Chain Callout Boxes.** These are step-by-step worked examples, set apart from the main text, that show multiple reasoning moves working together. A reasoning chain might look like:

> **Reasoning Chain: Why does salt dissolve in water?**
> 1. *COM-06 (Classify substance)*: NaCl is an ionic compound.
> 2. *STR-03 (Identify bond type)*: Na⁺ and Cl⁻ are held by ionic bonds.
> 3. *STR-11 (Assess polarity)*: Water is a polar molecule.
> 4. *NRG-02 (Compare interaction strengths)*: Water-ion attractions can overcome the ionic lattice energy.

These chains are where the reasoning-move approach pays off most visibly. Study them carefully.

**Practice Questions.** End-of-section questions are framed as reasoning exercises, not fact recall. Instead of "What is the atomic number of carbon?" you will see questions like "Given that carbon has 6 protons, use COM-03 to determine its position on the periodic table, then use STR-01 to predict how many bonds it typically forms." The goal is always to practice *using* the moves, not to test whether you memorized a number.

**Composition Pattern Capstones.** At the end of selected chapters, an extended section walks through one or two Composition Patterns --- multi-domain reasoning chains applied to real-world phenomena. These are the most challenging sections and the most rewarding. They are where you see the full power of your toolkit.

**Enrichment (E) Sections.** Some topics go a step beyond what is needed for the main narrative --- a deeper look at orbital shapes, a more precise definition of entropy, a brief detour into nuclear chemistry. These sections are marked with **(E)** and are entirely optional. Skipping them will not break any dependency chain. If your instructor assigns them, they will deepen your understanding; if not, you will not miss anything required for later chapters.

**Chapter Summary Tables.** Every chapter ends with a quick-reference table listing all reasoning moves introduced in that chapter, their identifiers, and a one-sentence description. Use these tables for review and for navigating back to specific moves when you need a refresher.

The most important piece of advice for reading this book: **trust the dependency chain.** If something feels confusing, the issue is almost always that a prior reasoning move needs review. The dependency annotations will tell you exactly where to look. Chemistry is not a subject where isolated facts suddenly click --- it is a subject where each move makes the next one possible. Work the chain, and the subject will open up.
