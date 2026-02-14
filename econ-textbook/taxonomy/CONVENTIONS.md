# CONVENTIONS v0.1

This document establishes the cross-domain conventions, traceability infrastructure, and quality standards governing all economics taxonomy files. It MUST be read before any domain spec and MUST be complete before any domain spec is authored.

---

## 1. Foundational Principles

### Principle 1: Closed Domain Catalog, Open Pattern Catalog

The **domain catalog is closed**: 5 domains (CHO, MKT, MAC, MON, POL). No 6th domain will be added. Any concept that appears to need a new domain MUST be resolved by: (a) assigning it to an existing domain via boundary principles (Section 5), or (b) documenting it as a composition pattern (Section 11).

The **composition pattern catalog is open**: new cross-domain results, policy applications, and interdisciplinary connections can be added indefinitely without restructuring the taxonomy.

New economics topics (behavioral economics, development economics, health economics, environmental economics) are **applications of existing domains**, not new domains. They deploy primitives from CHO, MKT, MAC, MON, and POL in combination, documented as composition patterns or application deployment patterns (Section 6).

### Principle 2: Reasoning-Move Standard

Every PRIM is a deployable cognitive operation statable as: **"Given [input], [operation] to determine [output]."** Every DEF is defined from previously listed PRIMs and DEFs. All items include a real-world hook grounding the concept in everyday, non-major contexts.

This standard ensures the taxonomy is not a topic list but a toolkit of transferable reasoning moves. A student who masters a PRIM can deploy it across contexts without re-learning the underlying logic.

### Principle 3: One Owner, Zero Redundancy

Every concept has **exactly one owning domain**. Other domains reference it, never redefine it. This is enforced by:
- Boundary principles P1--P5 (Section 5)
- Primitive Registry (Section 9)
- Redundancy detection procedure (Section 7)
- Self-audit checklists (Section 12)

### Principle 4: Non-Majors Calibration

Mathematical sophistication is capped: **algebra and basic graphical analysis only**. No calculus. Every item carries a **Tier annotation**:

| Tier | Meaning | Criterion |
|------|---------|-----------|
| **C** (Core) | Essential for economic literacy | Required for every student in a one-semester intro econ survey |
| **E** (Enrichment) | Valuable but cuttable | Can be omitted without breaking dependency chains |

Enrichment items MUST NOT be prerequisites for Core items. The Core tier alone MUST form a self-contained, dependency-complete sub-taxonomy.

---

## 2. No Metatheory Stratification Needed

Unlike the logic taxonomy, which requires a two-level metatheory stratification (naive metalanguage vs. formal object language), economics for non-majors operates at a single conceptual level. There is no meta/object-level distinction to manage: economic reasoning is about choices, prices, aggregate outcomes, money, and policy directly. No bootstrap domain is needed.

The closest analogy is that MAC (Macroeconomics) bridges between individual decisions and aggregate outcomes, but this is a **perspective shift within economics** (micro-to-macro aggregation), not a metalanguage/object-language stratification. Both perspectives describe the same economic reality at different scales.

---

## 3. Traceability ID Scheme

### Domain Codes (unambiguous, 3-letter)

| Code | Domain |
|------|--------|
| CHO | Choice |
| MKT | Markets |
| MAC | Macroeconomics |
| MON | Money & Banking |
| POL | Policy |
| GLB | Global (shared references in this document) |

### Item Type Prefixes

| Prefix | Meaning | Example |
|--------|---------|---------|
| PRIM | Primitive reasoning move (foundational) | PRIM-CHO001 |
| DEF | Definition (built from PRIMs/DEFs) | DEF-MKT003 |
| AX | Axiom (minimal; foundational postulates only) | AX-CHO001 |
| SRC | Source reference | SRC-GLB001 (global) or SRC-MKT001 (domain-specific) |
| ASM | Assumption | ASM-GLB001 (global) or ASM-CHO001 (domain-specific) |
| UNK | Unknown / open question | UNK-GLB001 |
| DEP | Dependency on another domain | DEP-MKT001 |
| EXT | Extension point | EXT-MAC001 |

### ID Format

All IDs follow the pattern `{TYPE}-{CODE}{NNN}`, e.g., `PRIM-CHO001`, `DEF-MKT003`, `AX-CHO001`.

### Cross-Domain Reference Format

References use the full format `{ItemType}-{DomainCode}{Number}`. When domain A references domain B's primitive, write `PRIM-CHO002` (not a local alias). The owning domain MUST list it in Exports; the referencing domain MUST list it in Imports.

### Source Reference Scoping

Global SRC entries (SRC-GLB001 through SRC-GLBNNN) live in this document and are shared across all domain specs. Domain-specific SRC entries (SRC-{D}NNN) live in their domain spec for sources relevant only to that domain. Domain specs MAY cite global SRCs by their GLB ID.

### ID Stability

IDs are permanent once assigned. Deprecated items use `DEPRECATED-{original-ID}` with pointer to replacement. IDs MUST NOT be renumbered across versions.

### Document Versioning

Domain specs use semantic versioning (v0.1 to v0.2 for non-breaking additions, v1.0 for first stable release). Breaking changes (removing/renaming primitives) require v(N+1).0 and a migration note listing all affected cross-references.

---

## 4. Normative Language

Per RFC 2119, used at full strength throughout all taxonomy documents:

- **MUST** / **MUST NOT** = structural requirement; violation means the taxonomy is broken or the reasoning move is misspecified
- **SHOULD** / **SHOULD NOT** = strong convention; deviation requires documented justification
- **MAY** = optional; extension point or instructor-specific

---

## 5. Boundary Principles (Ownership Disambiguation)

When a concept could belong to multiple domains, these principles resolve ownership:

| Principle | Rule | Example |
|-----------|------|---------|
| **P1 -- Individual vs. Market** | Decision-making by a single agent (person or firm) without price interaction --> CHO. Price formation, interaction among buyers/sellers, equilibrium --> MKT. | "opportunity cost" --> CHO. "equilibrium price" --> MKT. |
| **P2 -- Micro vs. Macro** | Behavior of individual markets (one good, one industry) --> MKT. Economy-wide aggregates (total output, general price level, total employment) --> MAC. | "supply curve for wheat" --> MKT. "GDP" --> MAC. |
| **P3 -- Real vs. Monetary** | Flows of goods, services, labor, and real output --> MAC. Money supply, interest rates, banking system mechanics --> MON. | "unemployment rate" --> MAC. "money multiplier" --> MON. |
| **P4 -- One Owner, Many References** | Every concept owned by one domain. Others import. | "interest rate" owned by MON. MAC and POL reference PRIM-MON003. |
| **P5 -- Mechanism vs. Intervention** | How a market or economy works (natural mechanism) --> MKT or MAC. Deliberate government action to change outcomes --> POL. | "externality" (market mechanism) --> MKT. "Pigouvian tax" (government intervention) --> POL. |

### Pre-Analyzed Ownership Splits for Contested Concepts

| Concept | Primary Owner | Secondary User | Connection |
|---------|---------------|----------------|------------|
| Interest rate | PRIM-MON003 (price of borrowing money) | MAC uses for aggregate demand; POL uses for monetary policy tool | MAC and POL import PRIM-MON003 |
| Price level | PRIM-MAC004 (aggregate price index) | MON connects money supply to price level | MON imports PRIM-MAC004 |
| Externality | DEF-MKT006 (market failure concept) | POL corrects via taxes/regulation | POL imports DEF-MKT006 |
| Tax | DEF-POL002 (policy instrument) | MKT analyzes incidence via supply/demand | MKT imports DEF-POL002 for tax incidence analysis (CP-003) |

**Governing rule**: CHO owns individual decision logic. MKT owns price coordination and market mechanisms. MAC owns aggregate outcomes. MON owns the financial system. POL owns government intervention. When a policy uses market reasoning, POL imports from MKT. When a macro outcome uses monetary mechanisms, MAC imports from MON.

---

## 6. Extension Protocol

New economics topics are NOT new domains. They are applications that deploy primitives from existing domains. The extension protocol works as follows:

| Application Area | Deployed Domains | Example Primitives Used |
|-----------------|-----------------|------------------------|
| Behavioral economics | CHO + MKT | PRIM-CHO001 (scarcity), PRIM-CHO003 (marginal analysis), AX-CHO001 (rationality) |
| Environmental economics | MKT + POL | DEF-MKT006 (externality), DEF-MKT007 (public good), PRIM-POL001 (market failure correction) |
| International economics | MKT + MAC + MON | PRIM-MKT003 (equilibrium), DEF-MAC005 (trade balance), DEF-MON004 (exchange rate) |
| Health economics | CHO + MKT + POL | PRIM-CHO001 (scarcity), PRIM-MKT005 (market structure), DEF-MKT006 (externality) |
| Development economics | CHO + MAC + POL | PRIM-CHO002 (opportunity cost), PRIM-MAC001 (GDP reasoning), PRIM-POL001 (market failure correction) |

To document a new application area:
1. Identify which existing PRIMs and DEFs from CHO, MKT, MAC, MON, POL are deployed
2. If a new composition pattern is needed, add it using the CP-NNN template (Section 11)
3. DO NOT create new domain codes or domain specs
4. Document the application as a deployment pattern in COMPOSITION-PATTERNS.md

---

## 7. Redundancy Detection Procedure

Run **after completing each domain spec** (partial check against existing registry) and **in full during the Reconciliation Pass**:

1. **Alphabetical cross-domain sort**: Export all PRIM and DEF entries from all domains into a single list sorted by concept name. Flag any name appearing in more than one domain.
2. **For each flagged name**: Apply boundary principles P1--P5. Determine: is this genuinely two different concepts, or an ownership violation (same concept defined twice)?
3. **If two different concepts**: Ensure both have distinct names, distinct IDs, and a documented cross-reference linking them via a composition pattern or import.
4. **If ownership violation**: Remove the duplicate from the non-owning domain. Replace with a REFERENCES annotation pointing to the owner's ID.
5. **Registry update**: After resolution, update the Primitive Registry (Section 9).

---

## 8. Iteration and Backtracking Protocol

Writing domain specs is not purely linear. When Step N reveals a needed change to Step M (M < N):

1. **Identify the change**: What primitive/definition in domain M needs to be added, modified, or have its ownership changed?
2. **Update domain M's spec**: Make the change, update the Primitive Registry, increment version (v0.1 to v0.2).
3. **Cascade check**: Search all domain specs written between M and N for references to the changed item. Update cross-references.
4. **Re-run self-audit**: Run the 10-item checklist on both the modified domain M and any domains with updated cross-references.
5. **Continue**: Resume Step N with the fix in place.

The Reconciliation Pass is the scheduled iteration point, but backtracking MAY happen at any step.

---

## 9. Primitive Registry

Single source of truth for all primitives and definitions across the taxonomy. Updated after each domain spec is completed. Total: 47 items (22 PRIM + 22 DEF + 3 AX).

### CHO -- Choice (5 PRIM + 3 DEF + 1 AX = 9 items)

| ID | Concept | Owner | Referenced By | Tier |
|----|---------|-------|---------------|------|
| PRIM-CHO001 | Scarcity reasoning | CHO | MKT, MAC, POL | C |
| PRIM-CHO002 | Opportunity cost reasoning | CHO | MKT, MAC, POL | C |
| PRIM-CHO003 | Marginal analysis | CHO | MKT, MAC, POL | C |
| PRIM-CHO004 | Incentive reasoning | CHO | MKT, POL | C |
| PRIM-CHO005 | Trade and specialization reasoning | CHO | MKT, MAC | C |
| DEF-CHO001 | Production possibilities frontier | CHO | MAC | C |
| DEF-CHO002 | Diminishing marginal returns | CHO | MKT | C |
| DEF-CHO003 | Comparative advantage | CHO | MKT, MAC | C |
| AX-CHO001 | Rational self-interest | CHO | MKT, MAC, MON, POL | C |

### MKT -- Markets (5 PRIM + 7 DEF = 12 items)

| ID | Concept | Owner | Referenced By | Tier |
|----|---------|-------|---------------|------|
| PRIM-MKT001 | Demand reasoning | MKT | MAC, POL | C |
| PRIM-MKT002 | Supply reasoning | MKT | MAC, POL | C |
| PRIM-MKT003 | Equilibrium reasoning | MKT | MAC, POL | C |
| PRIM-MKT004 | Elasticity reasoning | MKT | POL | C |
| PRIM-MKT005 | Market structure reasoning | MKT | POL | C |
| DEF-MKT001 | Demand curve | MKT | MAC | C |
| DEF-MKT002 | Supply curve | MKT | MAC | C |
| DEF-MKT003 | Price ceiling and floor | MKT | POL | C |
| DEF-MKT004 | Consumer and producer surplus | MKT | POL | C |
| DEF-MKT005 | Deadweight loss | MKT | POL | C |
| DEF-MKT006 | Externality | MKT | POL | C |
| DEF-MKT007 | Public good | MKT | POL | E |

### MAC -- Macroeconomics (5 PRIM + 5 DEF = 10 items)

| ID | Concept | Owner | Referenced By | Tier |
|----|---------|-------|---------------|------|
| PRIM-MAC001 | GDP reasoning | MAC | POL | C |
| PRIM-MAC002 | Unemployment reasoning | MAC | POL | C |
| PRIM-MAC003 | Inflation reasoning | MAC | MON, POL | C |
| PRIM-MAC004 | Price level reasoning | MAC | MON | C |
| PRIM-MAC005 | Business cycle reasoning | MAC | POL | C |
| DEF-MAC001 | Nominal vs. real values | MAC | MON | C |
| DEF-MAC002 | Aggregate demand | MAC | POL | C |
| DEF-MAC003 | Aggregate supply | MAC | POL | C |
| DEF-MAC004 | Multiplier effect | MAC | POL | E |
| DEF-MAC005 | Trade balance | MAC | POL | E |

### MON -- Money & Banking (4 PRIM + 4 DEF = 8 items)

| ID | Concept | Owner | Referenced By | Tier |
|----|---------|-------|---------------|------|
| PRIM-MON001 | Money functions reasoning | MON | MAC | C |
| PRIM-MON002 | Banking system reasoning | MON | MAC, POL | C |
| PRIM-MON003 | Interest rate reasoning | MON | MAC, POL | C |
| PRIM-MON004 | Money supply reasoning | MON | MAC, POL | C |
| DEF-MON001 | Fractional reserve banking | MON | POL | C |
| DEF-MON002 | Money multiplier | MON | POL | C |
| DEF-MON003 | Central bank operations | MON | POL | C |
| DEF-MON004 | Exchange rate | MON | MAC, POL | E |

### POL -- Policy (3 PRIM + 3 DEF + 2 AX = 8 items)

| ID | Concept | Owner | Referenced By | Tier |
|----|---------|-------|---------------|------|
| PRIM-POL001 | Market failure correction reasoning | POL | -- | C |
| PRIM-POL002 | Fiscal policy reasoning | POL | -- | C |
| PRIM-POL003 | Monetary policy reasoning | POL | -- | C |
| DEF-POL001 | Government budget and deficit | POL | -- | C |
| DEF-POL002 | Tax incidence | POL | -- | C |
| DEF-POL003 | Trade policy | POL | -- | E |
| AX-POL001 | Efficiency-equity tradeoff | POL | -- | C |
| AX-POL002 | No free lunch in policy | POL | -- | C |

---

## 10. Domain Dependency DAG

```
CHO (root -- no prerequisites)
 |-- MKT (depends: CHO)
 |-- MAC (depends: CHO, MKT)
 |-- MON (depends: CHO)
 +-- POL (depends: CHO, MKT, MAC, MON)
```

MKT and MON are **mutually independent**. MAC depends on CHO and MKT. POL depends on all four upstream domains.

**Topological sort (pedagogical order)**: CHO --> MKT --> MON --> MAC --> POL

Note: MAC depends on MKT (aggregate demand/supply build on market demand/supply) but NOT on MON. MON does not depend on MKT. MAC and MON can be taught in either order; the topological sort places MON before MAC for pedagogical convenience (understanding money before macro aggregates), though the reverse is also valid. POL comes last because it requires all prior domains.

### Independence Verification Arguments

Each independence claim below is supported by a non-trivial argument:

- **MKT does not depend on MON**: Supply, demand, equilibrium, elasticity, and market structure are defined using real goods and relative prices. No concept of money supply, banking, or interest rates is required to define how prices coordinate buyers and sellers. Barter economies have markets; money is not a prerequisite for market reasoning.

- **MON does not depend on MKT**: The functions of money (medium of exchange, store of value, unit of account), the banking system, the money supply, and interest rates are defined as properties of the financial system. They do not require supply-demand curves, elasticity, or market structure analysis. You can explain what money does, how banks create money, and what interest rates represent without analyzing a single supply-demand diagram.

- **MON does not depend on MAC**: Money, banking, and interest rates are defined as financial system mechanics. GDP, unemployment, and inflation reasoning are not prerequisites for understanding what money is, how fractional reserve banking works, or why interest rates exist. Money existed before anyone measured GDP.

- **MAC does not depend on MON**: GDP, unemployment, inflation, the price level, and business cycles can be defined as aggregate outcomes without reference to the banking system or money supply. Real GDP measures output of goods and services; unemployment measures labor market slack; inflation measures the rate of price-level change. These are measurable aggregates that do not require understanding of how banks create money or how the central bank operates.

---

## 11. Composition Pattern Template

Composition patterns document cross-domain reasoning chains that integrate primitives from multiple domains. Each pattern follows this format:

```markdown
### CP-NNN: **{Pattern Name}**

- **Domains**: {DomainCode} x {DomainCode} [x ...]
- **Statement**: [what this pattern accomplishes]
- **Natural language**: [explanation, >= 1 sentence]
- **Key dependencies**: [list of PRIM/DEF IDs from each involved domain]
- **Real-world hook**: [everyday context where this pattern is deployed]
- **Tier**: C or E
- **Significance**: [why this cross-domain integration matters]
```

### Registered Composition Patterns

Seven composition patterns are registered. Full specifications live in COMPOSITION-PATTERNS.md.

| ID | Name | Domains | Tier |
|----|------|---------|------|
| CP-001 | How Prices Allocate Scarce Resources | CHO x MKT | C |
| CP-002 | Why Trade Makes Both Sides Better Off | CHO x MKT x MAC | C |
| CP-003 | Tax Incidence and Deadweight Loss | MKT x POL | C |
| CP-004 | How the Fed Fights Recession | MON x MAC x POL | C |
| CP-005 | The Minimum Wage Debate | CHO x MKT x POL | C |
| CP-006 | Inflation and the Cost of Living | MAC x MON | C |
| CP-007 | Correcting Pollution Externalities | MKT x POL | C |

---

## 12. Self-Audit Checklist

Every domain spec MUST pass all 10 items before being considered complete:

- [ ] Every PRIM has: reasoning move formulation ("Given X, do Y to determine Z"), description, semi-formal statement, depends, ownership, source, referenced-by, tier, real-world hook
- [ ] Every DEF depends only on previously listed PRIM/DEF (check intra-domain dependency graph)
- [ ] Every cross-domain reference uses full `{Type}-{Code}{Number}` format
- [ ] Every import is listed in the source domain's exports
- [ ] Dissolution argument is present and non-trivial (at least 2 sentences explaining why this domain is distinct)
- [ ] Real-world hooks cover everyday non-major contexts (grocery shopping, job decisions, news headlines, personal finance, voting)
- [ ] Intra-domain dependency graph is acyclic
- [ ] Tier annotations (C/E) are present on all items
- [ ] No PRIM/DEF duplicates an entry in another domain (checked against Primitive Registry)
- [ ] Reasoning moves are genuinely "Given X, do Y" cognitive operations (not mere topic labels or vocabulary words)

---

## 13. Economics Education Research Mapping

This section maps established economics education research frameworks onto the taxonomy's domain structure, ensuring that the 5-domain architecture is not arbitrary but aligns with independently validated conceptual dimensions.

### Threshold Concepts in Economics (Davies & Mangan, 2007)

| Threshold Concept | Primary Domain | Key Primitives |
|-------------------|---------------|----------------|
| Opportunity cost | CHO | PRIM-CHO002 (opportunity cost reasoning) |
| Equilibrium | MKT | PRIM-MKT003 (equilibrium reasoning) |
| Elasticity | MKT | PRIM-MKT004 (elasticity reasoning) |
| Multiplier | MAC | DEF-MAC004 (multiplier effect) |
| Comparative advantage | CHO | DEF-CHO003 (comparative advantage) |

### TUCE (Test of Understanding in College Economics) Dimensions

| TUCE Category | Domain Mapping | Key Primitives |
|---------------|---------------|----------------|
| Basic economic concepts | CHO | PRIM-CHO001, PRIM-CHO002, PRIM-CHO003 |
| Markets and price determination | MKT | PRIM-MKT001, PRIM-MKT002, PRIM-MKT003 |
| National income and macro measurement | MAC | PRIM-MAC001, PRIM-MAC002, PRIM-MAC003 |
| Money and banking | MON | PRIM-MON001, PRIM-MON002, PRIM-MON004 |
| Stabilization policy | POL | PRIM-POL002, PRIM-POL003 |
| International economics | Cross-domain | CP-002 (trade), DEF-MON004 (exchange rate) |

### Siegfried et al. "Vital and Large" Economic Concepts (1991)

| Concept | Domain(s) | Role |
|---------|-----------|------|
| Scarcity | CHO | PRIM-CHO001 -- the root concept of all economics |
| Opportunity cost | CHO | PRIM-CHO002 -- the hidden cost of every decision |
| Marginalism | CHO | PRIM-CHO003 -- the framework for rational optimization |
| Voluntary exchange | MKT | PRIM-MKT003, DEF-MKT004 -- both sides gain from trade |
| Market failure | MKT + POL | DEF-MKT006, PRIM-POL001 -- when and why markets fail to optimize |

---

## 14. Global Sources (SRC-GLB)

| ID | Reference |
|----|-----------|
| SRC-GLB001 | OpenStax, *Principles of Economics*, 3rd ed., 2023 (CC-BY 4.0) |
| SRC-GLB002 | Mankiw, *Principles of Economics*, 9th ed., 2021 |
| SRC-GLB003 | CORE Econ, *The Economy*, 2017 (open access) |
| SRC-GLB004 | Siegfried et al., "The Status and Prospects of the Economics Major," *J. Economic Education*, 1991 |
| SRC-GLB005 | Davies & Mangan, "Threshold concepts and the integration of understanding in economics," *Studies in Higher Education*, 2007 |
| SRC-GLB006 | Walstad & Rebeck, *Test of Understanding in College Economics (TUCE)*, 4th ed., 2008 |
| SRC-GLB007 | Samuelson & Nordhaus, *Economics*, 19th ed., 2010 |
| SRC-GLB008 | Becker, "The Economic Approach to Human Behavior," 1976 (rational choice foundation) |

---

## 15. Global Assumptions (ASM-GLB)

| ID | Assumption | Justification |
|----|-----------|---------------|
| ASM-GLB001 | Target audience is non-majors in a one-semester intro economics survey | Design constraint from project brief |
| ASM-GLB002 | No calculus; algebra, graphs, and proportional reasoning only | Math ceiling for non-majors; graphical supply-demand analysis is sufficient for all Core-tier items |
| ASM-GLB003 | Economic literacy = ability to reason about tradeoffs, evaluate policy claims, and understand news headlines about the economy | Core design goal: students should be able to read a news article about inflation or trade policy and reason about it using named primitives |
| ASM-GLB004 | Applications are deployment exercises for named primitives, not the organizational backbone | Solves the situatedness paradox: contexts motivate but do not define the curriculum architecture |
| ASM-GLB005 | Political neutrality: the taxonomy identifies reasoning patterns, not policy conclusions | The same primitives (marginal analysis, incentive reasoning, tradeoff analysis) can support different policy positions depending on empirical assumptions |

---

## 16. Global Unknowns (UNK-GLB)

| ID | Unknown | Impact |
|----|---------|--------|
| UNK-GLB001 | Optimal depth of international economics: should exchange rates and trade balance be Core or Enrichment? | Currently trade balance (DEF-MAC005) and exchange rate (DEF-MON004) are Enrichment. If pilot testing shows students cannot reason about globalization news without them, promote to Core. |
| UNK-GLB002 | Should behavioral economics deviations from rationality (e.g., bounded rationality, cognitive biases) be an explicit PRIM in CHO or handled as a qualification of AX-CHO001? | Currently handled as a qualification. If students systematically fail to recognize when the rationality axiom breaks down, promote to separate item. |
| UNK-GLB003 | How deep should inequality/poverty treatment go? Currently no explicit PRIM; it is a cross-domain application of MKT (labor markets) + POL (redistribution). | If pilot testing reveals students need an explicit poverty-reasoning primitive to evaluate welfare policy claims, add a DEF to POL. |

---

## 17. Worked Example: One Fully Specified Entry

This demonstrates exactly what a completed entry looks like in a domain spec:

- PRIM-CHO002: **Opportunity cost reasoning**
  - Reasoning move: Given a decision between two or more alternatives, identify the value of the best forgone alternative to determine the true cost of the chosen option.
  - Description: The cognitive operation of recognizing that every choice has a hidden cost: not just the money spent, but the value of the next-best thing you gave up. Opportunity cost is the single most important reasoning move in economics because it transforms "how much does this cost?" from a simple price-tag question into a deeper analysis of tradeoffs. A student who goes to college does not just pay tuition -- they forgo the wages they could have earned. A city that builds a stadium does not just spend tax dollars -- it forgoes the school or hospital it could have built instead.
  - Semi-formal: For decision-maker D choosing option A from set {A, B, C, ...}, the opportunity cost of A = value(best forgone alternative). If D chooses A, OC(A) = max(value(B), value(C), ...). The total economic cost of A = explicit cost(A) + OC(A).
  - Depends: PRIM-CHO001 (scarcity reasoning -- opportunity cost exists because resources are scarce; without scarcity, there are no tradeoffs)
  - Ownership: CHO
  - Source: SRC-GLB001 (OpenStax Ch. 1--2), SRC-GLB002 (Mankiw Ch. 1), SRC-GLB005 (Davies & Mangan 2007, threshold concept)
  - Referenced by: MKT, MAC, POL
  - Tier: C
  - Real-world hook: When you spend Friday evening studying for an exam instead of going to a concert, the opportunity cost of studying is the enjoyment of the concert. The cost of college is not just tuition -- it includes the four years of salary you did not earn. Recognizing opportunity cost changes how you evaluate every decision.

Every item in every domain spec MUST match this level of detail.
