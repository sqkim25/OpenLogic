# 03-GAP-ANALYSIS v0.1

> Phase 2 Gap Analysis | Source: OpenStax *Principles of Economics* 3e (SRC-GLB001)
> Taxonomy: 5 domains, 47 items, 7 CPs (see `../taxonomy/CONVENTIONS.md`)

---

## 1. Taxonomy Items with Insufficient Source Coverage

### 1.1 Items Requiring Strengthening (PARTIAL or IMPLICIT)

No ABSENT items exist. Three items have coverage below FULL and require authorial work in Phase 3.

| Item | Coverage | Gap Description | Classification | Action |
|------|----------|----------------|----------------|--------|
| DEF-POL002 (Tax incidence) | PARTIAL | OpenStax discusses tax incidence in the externality chapter (Ch 12) and the elasticity chapter (Ch 5) but never delivers the full formal treatment: the elasticity formula for burden sharing (buyer share = E_s / (E_s + E_d)), the independence of incidence from legal assignment, and the DWL calculation for an arbitrary tax. | REQUIRES-STRENGTHENING | In Phase 3, write a complete tax incidence treatment combining Ch 5 elasticity framework with Ch 12 tax mechanics. Source from SRC-GLB002 (Mankiw Ch 8) which provides the full treatment. |
| AX-POL001 (Efficiency-equity tradeoff) | IMPLICIT | OpenStax invokes this tradeoff repeatedly (Ch 15 poverty, Ch 18 public economy, Ch 32 fiscal policy) but never states it as an explicit principle. Students encounter the tradeoff but are never given the named axiom as a tool for structured policy analysis. | REQUIRES-EXPLICITATION | In Phase 3, add an explicit axiom statement in the POL chapter, referencing Okun (SRC-POL003). Not a new concept -- just making an implicit principle explicit. |
| AX-POL002 (No free lunch in policy) | IMPLICIT | Same pattern: OpenStax assumes this throughout but never states it as a named principle. Mankiw's "Ten Principles" (SRC-GLB002, Principle 1) states it explicitly. | REQUIRES-EXPLICITATION | In Phase 3, add an explicit axiom statement in the POL chapter. |

**Backtracking assessment**: 0 ABSENT items. 3 items need strengthening/explicitation but all have sufficient source material to work from. No backtracking to Phase 1 required.

### 1.2 Items Fully Covered

44 of 47 taxonomy items have FULL coverage from the OpenStax source. See `02-COVERAGE-MATRIX.md` for the complete table.

---

## 2. OpenStax Topics Not in Taxonomy (Out-of-Scope)

The following OpenStax topics have no corresponding taxonomy item. Each is classified as either a deployment exercise for existing primitives, pedagogical context, or genuinely out-of-scope.

### 2.1 Deployment Exercises (Covered by Existing Primitives)

These topics are NOT gaps -- they are applications of existing taxonomy items in specific contexts.

| OpenStax Topic | Chapter(s) | Taxonomy Items Deployed | Classification |
|---------------|-----------|------------------------|----------------|
| Utility theory (marginal utility, budget constraint) | Ch 6 | PRIM-CHO003 (marginal analysis), PRIM-CHO001 (scarcity via budget constraint) | DEPLOYMENT of CHO primitives in consumer context |
| Cost curves (MC, ATC, AVC, long-run) | Ch 7 | DEF-CHO002 (diminishing marginal returns), PRIM-CHO003 (marginal analysis) | DEPLOYMENT of CHO primitives in firm context |
| Oligopoly game theory (prisoner's dilemma, Nash equilibrium) | Ch 10 | PRIM-MKT005 (market structure), PRIM-CHO004 (incentive reasoning) | DEPLOYMENT -- game theory is a formalism for strategic incentive reasoning |
| Labor market analysis (wage determination, discrimination) | Ch 14 | PRIM-MKT001, PRIM-MKT002, PRIM-MKT003 (S/D applied to labor) | DEPLOYMENT of MKT primitives in labor context |
| Poverty measurement (Gini, poverty line, safety net programs) | Ch 15 | AX-POL001 (efficiency-equity tradeoff), PRIM-POL002 (fiscal policy: redistribution) | DEPLOYMENT of POL axioms and primitives |
| Economic growth models (Solow, productivity, convergence) | Ch 22 | PRIM-MAC001 (GDP reasoning), DEF-MAC003 (AS: LRAS shift), DEF-CHO001 (PPF: outward shift) | DEPLOYMENT of MAC/CHO items for growth |
| Keynesian cross model | Ch 27 | DEF-MAC002 (aggregate demand), DEF-MAC004 (multiplier effect) | STEPPING-STONE -- the cross is the pedagogical vehicle for the multiplier |
| Automatic stabilizers | Ch 32 | PRIM-POL002 (fiscal policy), PRIM-CHO004 (incentive reasoning) | DEPLOYMENT of POL/CHO primitives |

### 2.2 Pedagogical Context (Non-Definitional)

These sections provide motivation, history, or narrative context. They do not define reasoning moves.

| OpenStax Topic | Chapter(s) | Classification |
|---------------|-----------|----------------|
| History of money (barter, commodity, fiat) | Ch 29 | PEDAGOGICAL hook for PRIM-MON001 |
| GDP limitations (does not count household work, leisure, environment) | Ch 21 | PEDAGOGICAL qualification of PRIM-MAC001 |
| Great Depression / Great Recession case studies | Ch 26, 27 | PEDAGOGICAL deployment of MAC/POL reasoning |
| Federal Reserve structure and governance | Ch 30 | PEDAGOGICAL institutional context for DEF-MON003 |
| WTO, NAFTA/USMCA, EU economic integration | Ch 20, 33 | PEDAGOGICAL context for DEF-POL003 |
| Voting theory, public choice, government failure | Ch 18 | PEDAGOGICAL context for AX-POL002 and ASM-POL002 |
| Personal finance (savings, retirement, insurance) | Ch 16, 17 | PEDAGOGICAL -- practical but not a reasoning primitive |
| Say's Law, rational expectations | Ch 28 | PEDAGOGICAL -- historical schools of thought |

### 2.3 Genuinely Out-of-Scope

These topics require reasoning moves not captured by the 47-item taxonomy. They are documented here as potential extension points (per CONVENTIONS.md Section 6) but are NOT added to the taxonomy.

| OpenStax Topic | Chapter(s) | Missing Reasoning Move | Resolution |
|---------------|-----------|----------------------|------------|
| Information asymmetry (moral hazard, adverse selection) | Ch 16 | Asymmetric information as a distinct market failure type beyond externality/public good | **NOT added.** Per CONVENTIONS.md Section 6, information economics is an application area deploying CHO (incentive reasoning) + MKT (market failure). At non-majors depth, asymmetric information is adequately treated as a qualification of PRIM-MKT005 (market structure) and a case for PRIM-POL001 (market failure correction). If pilot testing reveals students cannot reason about insurance markets or used car markets without an explicit information asymmetry primitive, promote to a new DEF-MKT item (see UNK below). |
| Common resources (tragedy of the commons) | Ch 13 | Rivalrous but non-excludable goods as distinct from public goods | **NOT added.** Common resources are analyzable as the intersection of DEF-MKT006 (externality: overuse imposes costs on others) and PRIM-CHO004 (incentive to overuse because no exclusion). Not a separate primitive at non-majors level. |
| Behavioral economics (bounded rationality, biases) | Ch 6 (briefly) | Systematic deviations from AX-CHO001 | **NOT added.** Per UNK-GLB002 in CONVENTIONS.md, this is handled as a qualification of AX-CHO001. Promotion to a separate item is deferred to pilot testing. |

### 2.4 New UNK Items from Gap Analysis

| ID | Unknown | Source | Impact |
|----|---------|--------|--------|
| UNK-GLB004 | Should information asymmetry (moral hazard, adverse selection) be a DEF in MKT? | OpenStax Ch 16 covers this at length; taxonomy currently treats it as a deployment exercise. | Low for non-majors core. If added, it would be DEF-MKT008 (Enrichment tier). Monitor during pilot. |

This is the only gap candidate identified. Since it is 1 item (well below the 5-item "concept explosion" threshold from `02-MAPPING.md` Section 5.3), it does not trigger the Phase 2.5 resolution protocol.

---

## 3. Linearization Decision

### 3.1 Topological Order (from CONVENTIONS.md Section 10)

The taxonomy's dependency DAG dictates: **CHO --> MKT --> MON --> MAC --> POL**

### 3.2 Proposed Lean Text Chapter Sequence

Mapping the 34 OpenStax chapters onto the topological order, with compression applied:

| Lean Ch | Title | OpenStax Source | Taxonomy Items Introduced | Signal |
|---------|-------|----------------|---------------------------|--------|
| **1** | Scarcity, Choice, and Tradeoffs | Ch 1 + Ch 2 | PRIM-CHO001, PRIM-CHO002, PRIM-CHO003, PRIM-CHO004, DEF-CHO001, DEF-CHO002, AX-CHO001 | Merge two OpenStax chapters into one lean chapter covering all CHO items except trade |
| **2** | Specialization and Trade | Ch 19 (theory) | PRIM-CHO005, DEF-CHO003 | Comparative advantage moved to CHO domain per taxonomy ownership; OpenStax places it in Ch 19 |
| **3** | Demand, Supply, and Equilibrium | Ch 3 | PRIM-MKT001, PRIM-MKT002, PRIM-MKT003, DEF-MKT001, DEF-MKT002, DEF-MKT003 | Core MKT chapter; largely adapt Ch 3 |
| **4** | Elasticity | Ch 5 | PRIM-MKT004 | Focused chapter; adapt Ch 5 |
| **5** | Market Efficiency and Surplus | Ch 8 (welfare) | DEF-MKT004, DEF-MKT005 | Surplus and DWL from the perfect competition welfare analysis |
| **6** | Market Structure | Ch 8 + Ch 9 + Ch 10 | PRIM-MKT005 | Compressed: perfect competition benchmark, monopoly as deviation, brief monopolistic competition and oligopoly |
| **7** | Market Failures: Externalities and Public Goods | Ch 12 + Ch 13 | DEF-MKT006, DEF-MKT007 | Completes the MKT domain |
| **8** | Money and Banking | Ch 29 | PRIM-MON001, PRIM-MON002, PRIM-MON004, DEF-MON001, DEF-MON002 | Core MON items; money functions through money multiplier |
| **9** | Interest Rates and Central Banking | Ch 30 | PRIM-MON003, DEF-MON003 | Interest rate reasoning and Fed operations |
| **10** | Measuring the Macroeconomy | Ch 21 + Ch 23 + Ch 24 | PRIM-MAC001, PRIM-MAC002, PRIM-MAC003, PRIM-MAC004, DEF-MAC001 | GDP + unemployment + inflation in one measurement chapter |
| **11** | Aggregate Demand and Aggregate Supply | Ch 26 | DEF-MAC002, DEF-MAC003, PRIM-MAC005 | The AD/AS model and business cycle reasoning |
| **12** | Market Failure Correction and Regulation | Ch 11 + Ch 12 (policy parts) + Ch 13 (policy parts) | PRIM-POL001, DEF-POL002 | Microeconomic policy: externality correction, antitrust, tax incidence |
| **13** | Fiscal Policy and the Government Budget | Ch 32 + Ch 27 (multiplier) | PRIM-POL002, DEF-POL001, DEF-MAC004 | Fiscal policy reasoning, budget/deficit, multiplier |
| **14** | Monetary Policy | Ch 30 (policy parts) | PRIM-POL003 | Monetary policy deployment (the POL side of Ch 30) |
| **15** | Trade Policy and Globalization | Ch 20 | DEF-POL003 | Trade restrictions and welfare analysis |
| **E1** | Exchange Rates *(Enrichment)* | Ch 31 | DEF-MON004 | Optional chapter; Enrichment tier |
| **E2** | Trade Balance and Capital Flows *(Enrichment)* | Ch 19 (macro parts) + Ch 25 | DEF-MAC005 | Optional chapter; Enrichment tier |
| -- | Axioms: Efficiency-Equity and No Free Lunch | Woven into Ch 12--15 | AX-POL001, AX-POL002 | Not a separate chapter; stated explicitly in the POL chapters as named axioms |

### 3.3 Compression Ratio

| Metric | OpenStax | Lean Text |
|--------|----------|-----------|
| Total chapters | 34 | 15 core + 2 enrichment = 17 |
| Reduction | -- | 50% chapter count reduction |
| Items per chapter (avg) | 1.4 | 3.1 (core items packed more densely) |
| Duplicate/overlap chapters eliminated | Ch 6, 7, 10 (partially), 14, 15, 16, 17, 18, 22, 25, 28, 33, 34 | 13 chapters absorbed or eliminated |

### 3.4 Linearization Rationale

1. **CHO first (Lean Ch 1--2)**: Root domain. No prerequisites. Establishes scarcity, opportunity cost, marginal analysis, incentives, PPF, comparative advantage. Trade/specialization gets its own chapter because it is the most counterintuitive CHO concept and involves a quantitative procedure (OC comparison).

2. **MKT second (Lean Ch 3--7)**: Depends only on CHO. Supply/demand/equilibrium is the central micro tool. Elasticity follows immediately (deepens S/D). Surplus and DWL establish the welfare framework. Market structure shows when the competitive benchmark fails. Externalities and public goods complete the market failure diagnosis.

3. **MON third (Lean Ch 8--9)**: Depends only on CHO. Placed before MAC in the topological sort for pedagogical convenience: students understand money and banking before encountering aggregate outcomes that monetary forces influence. Two chapters: money mechanics (Ch 8) and interest rates / central bank (Ch 9).

4. **MAC fourth (Lean Ch 10--11)**: Depends on CHO and MKT. Measurement chapter covers GDP, unemployment, inflation in one pass. AD/AS model chapter formalizes the business cycle and sets up policy analysis.

5. **POL last (Lean Ch 12--15)**: Depends on all four upstream domains. Micro policy (Ch 12: market failure correction, tax incidence), macro policy (Ch 13: fiscal, Ch 14: monetary), and trade policy (Ch 15). The two axioms (AX-POL001, AX-POL002) are stated explicitly in the opening of the POL section.

---

## 4. Open Decisions for Phase 3

### 4.1 Confirmed Decisions

| Decision | Resolution | Rationale |
|----------|-----------|-----------|
| Domain catalog | Closed at 5 (CHO, MKT, MAC, MON, POL) | No new domains needed; all OpenStax content maps to existing domains or is a deployment exercise |
| Item catalog | Closed at 47 + 7 CPs | One possible addition (information asymmetry) deferred to pilot testing |
| Linearization | CHO --> MKT --> MON --> MAC --> POL | Matches topological sort from CONVENTIONS.md Section 10 |
| Enrichment items | DEF-MKT007, DEF-MAC004, DEF-MAC005, DEF-MON004, DEF-POL003 | All 5 Enrichment items have FULL source coverage and can be optional chapters or appendices |

### 4.2 Decisions Requiring Phase 3 Resolution

| Decision | Options | Recommendation |
|----------|---------|----------------|
| **DEF-POL002 depth** | (a) Write a standalone tax incidence section from Mankiw; (b) Integrate into the elasticity chapter as an application | (b) Integrate into Lean Ch 4 (Elasticity) as the policy application of elasticity reasoning, with a forward reference from Lean Ch 12 (Policy). This keeps elasticity and its most important application together. |
| **AX-POL001/002 placement** | (a) Separate axiom section at the start of POL; (b) Inline as boxed principles when first needed | (a) State both axioms at the opening of the POL section (Lean Ch 12) as named principles, then reference them throughout Ch 12--15. This makes the axioms visible and nameable, which is the whole point of moving them from IMPLICIT to EXPLICIT. |
| **Utility theory treatment** | (a) Include as a optional appendix; (b) Drop entirely and rely on marginal analysis (PRIM-CHO003) | (b) Drop. At the non-majors level, "marginal benefit vs. marginal cost" is sufficient without formalizing it as "marginal utility per dollar equalized." The utility framework is a mathematical formalization that adds precision but not new reasoning power for non-majors. |
| **Game theory treatment** | (a) Include a brief oligopoly game theory section; (b) Drop and describe oligopoly behavior qualitatively | (b) Drop formal game theory. Describe oligopoly as "few firms with strategic interdependence" and give the intuition (firms consider rivals' reactions). The prisoner's dilemma is a powerful analogy but not a taxonomy item. |
| **Labor market chapter** | (a) Dedicated labor market chapter; (b) Integrate as S/D application | (b) Integrate. Labor markets are a deployment of MKT primitives. Include a brief labor market example in Lean Ch 3 (S/D) and reference in Lean Ch 12 (minimum wage via CP-005). |
| **Composition pattern deployment** | (a) Weave CPs into relevant chapters; (b) Collect as a capstone chapter | (a) Weave. Each CP should appear in the chapter where its latest required primitive is introduced. CP-001 in Lean Ch 3, CP-002 in Lean Ch 2, CP-003 in Lean Ch 12, CP-004 in Lean Ch 14, CP-005 in Lean Ch 12, CP-006 in Lean Ch 10, CP-007 in Lean Ch 12. |

---

## 5. Quality Gate 2 Results

| Check | Criterion | Result |
|-------|-----------|--------|
| QG2-1 | Coverage completeness: every item != ABSENT or documented | **PASS** -- 0 ABSENT items. 3 items (PARTIAL/IMPLICIT) are documented with strengthening plan. |
| QG2-2 | No orphan sections: every chapter has Introduces or References | **PASS** -- all 34 chapters are tagged. No orphan chapters. |
| QG2-3 | Redundancy resolution: every multi-section item has a canonical section | **PASS** -- 15 items with redundancy all have canonical sections designated in `02-COVERAGE-MATRIX.md`. |
| QG2-4 | Formal item classification: all formal blocks mapped | **PASS** -- OpenStax does not use formal `\begin{defn}` blocks; all conceptual definitions are mapped to taxonomy IDs or classified as deployment/pedagogical. |
| QG2-5 | Backtracking threshold: ABSENT + UNCERTAIN <= 20% | **PASS** -- 0% (0/47). |
| QG2-6 | Gap resolution: all gap candidates resolved | **PASS** -- 1 gap candidate (information asymmetry) documented as UNK-GLB004 and deferred. Below the 5-item threshold. |
| QG2-7 | Reverse index consistency: every section in coverage matrix maps back to source map | **PASS** -- all canonical chapters in `02-COVERAGE-MATRIX.md` are tagged in `01-OPENSTAX-ECON-MAP.md`. |

**Overall Quality Gate 2: PASS (7/7 checks)**

Phase 2 is complete. Proceed to Phase 3 (Compression).
