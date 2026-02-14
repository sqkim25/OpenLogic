# Principles of Economics: A Lean Text

*A compressed, reasoning-first introduction to economics for non-majors*

---

## Preface

This book is built differently from a standard economics textbook. Most introductory economics texts organize around topics: here is a chapter on supply and demand, here is a chapter on GDP, here is a chapter on monetary policy. The result is comprehensive but sprawling -- 30+ chapters, each introducing concepts that overlap, recur, and tangle with concepts from other chapters. Students finish the course with exposure to many economic topics but often without a clear mental framework for connecting them.

This book takes a different approach. It is organized around **reasoning moves** -- the small number of foundational cognitive operations that economists use to analyze the world. There are 47 of them, grouped into 5 domains. Every chapter introduces a specific set of reasoning moves, builds them from previously established ones, and shows how they deploy in real-world contexts. No concept is introduced twice. No concept is used before it is defined. Every item is traceable to its prerequisites.

The result is a leaner text: 15 core chapters and 2 optional enrichment chapters, covering the same intellectual territory as a standard 34-chapter textbook but without the redundancy. The tradeoff is breadth of examples -- we include fewer case studies and historical narratives. The payoff is conceptual clarity: after working through this book, you should be able to pick up any standard economics textbook, any news article about the economy, or any policy debate and locate the reasoning moves being deployed.

### Who This Book Is For

This book is for students taking a one-semester survey course in economics who are not planning to major in the subject. The mathematical ceiling is algebra and basic graphical reasoning -- no calculus. The goal is not to train economists but to produce economically literate citizens: people who can evaluate a politician's claim about trade policy, understand why the Federal Reserve raised interest rates, or reason about whether a minimum wage increase will help or hurt low-wage workers.

### How to Use This Book

Each chapter introduces named reasoning moves, marked with ID codes (like PRIM-CHO001 for "scarcity reasoning"). These codes are not bureaucratic decoration -- they are traceability tools. When a later chapter references an earlier concept, the ID tells you exactly where it was introduced and what it depends on. If you feel lost, the dependency annotation ("*Depends on: PRIM-CHO002, Chapter 1*") tells you exactly where to look.

Look for three recurring elements:

1. **Reasoning-move blockquotes**: Indented statements beginning "Given X, do Y to determine Z." These are the core cognitive operations -- the economic equivalent of a chemist's lab techniques.

2. **Reasoning Chain callout boxes**: Multi-step worked examples showing how multiple reasoning moves combine to answer a real-world question. These demonstrate the payoff of mastering individual moves.

3. **Practice Questions**: Each major section ends with questions that require deploying the reasoning moves, not just recalling definitions.

---

## Your Economic Toolkit

### The Five Domains

Economics reasoning decomposes into five domains, each answering a different governing question:

| Domain | Code | Governing Question | Items | Chapters |
|--------|------|-------------------|-------|----------|
| **Choice** | CHO | How do individuals and firms decide? | 9 | 1 |
| **Markets** | MKT | How do prices coordinate decisions? | 12 | 3--7 |
| **Money & Banking** | MON | How does the financial system work? | 8 | 8--9 |
| **Macroeconomics** | MAC | How does the economy behave in aggregate? | 10 | 10--11 |
| **Policy** | POL | When and how should government intervene? | 8 | 12--15 |
| | | **Total** | **47** | **15 core + 2 enrichment** |

### The Dependency Diagram

The domains are not independent -- they build on each other in a specific order. This diagram shows which domains must be understood before which:

```
CHO (Choice)
 |
 |--- root: no prerequisites
 |
 +---> MKT (Markets)
 |       depends on: CHO
 |
 +---> MON (Money & Banking)
 |       depends on: CHO
 |
 +---> MAC (Macroeconomics)
 |       depends on: CHO, MKT
 |
 +---> POL (Policy)
         depends on: CHO, MKT, MAC, MON
```

**Reading the diagram**: An arrow from A to B means "B requires concepts from A." CHO is the root -- it depends on nothing. MKT and MON both depend on CHO but not on each other. MAC depends on CHO and MKT. POL depends on everything.

**Pedagogical order**: CHO --> MKT --> MON --> MAC --> POL. This is the topological sort of the dependency graph. You can rearrange MON and MAC (since neither depends on the other), but CHO must come first and POL must come last.

### The Seven Composition Patterns

Some of the most important economic reasoning requires combining tools from multiple domains. These cross-domain reasoning chains are called **composition patterns**:

| ID | Pattern | Domains | Real-World Hook |
|----|---------|---------|-----------------|
| CP-001 | How Prices Allocate Scarce Resources | CHO x MKT | How does a grocery store know how much bread to stock? |
| CP-002 | Why Trade Makes Both Sides Better Off | CHO x MKT x MAC | Why do Americans buy Colombian roses? |
| CP-003 | Tax Incidence and Deadweight Loss | MKT x POL | Who really pays the cigarette tax? |
| CP-004 | How the Fed Fights Recession | MON x MAC x POL | What did the Fed do during COVID-19? |
| CP-005 | The Minimum Wage Debate | CHO x MKT x POL | Should the minimum wage be $15/hour? |
| CP-006 | Inflation and the Cost of Living | MAC x MON | Why did inflation spike to 9% in 2022? |
| CP-007 | Correcting Pollution Externalities | MKT x POL | What is the best way to reduce carbon emissions? |

These patterns appear as Reasoning Chain callout boxes throughout the text, deployed in the chapter where their last required concept is introduced.

### Core vs. Enrichment

Every item in the taxonomy is tagged as **Core** (essential for economic literacy) or **Enrichment** (valuable but cuttable). The 42 Core items form a self-contained sub-text: no Core item depends on an Enrichment item. Sections and chapters marked "Enrichment" can be skipped without breaking the logical flow.

---

*We begin with the most fundamental question in all of economics: Why can't you have everything you want?*
