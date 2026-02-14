# 02-COVERAGE-MATRIX v0.1

> Phase 2 Coverage Matrix | Source: OpenStax *Principles of Economics* 3e (SRC-GLB001)
> Taxonomy: 5 domains, 47 items, 7 CPs (see `../taxonomy/CONVENTIONS.md`)

---

## Methodology

For each of the 47 taxonomy items (22 PRIM + 22 DEF + 3 AX), this matrix records:
- **Canonical section**: The OpenStax chapter that provides the authoritative treatment
- **Other sections**: Additional chapters that reference or partially cover the item
- **Coverage**: FULL (formally introduced and developed) | PARTIAL (introduced but incompletely developed) | IMPLICIT (used without formal treatment) | ABSENT (not covered)
- **Redundancy**: None | EXPECTED (different contexts justify repetition) | COMPRESSION-TARGET (merge into canonical)

### Coverage Decision Tree Applied

- FULL = the chapter provides a definition, explanation, and examples that match the taxonomy's specification
- PARTIAL = the chapter introduces the concept but does not develop it to the depth the taxonomy requires
- IMPLICIT = the concept is used in reasoning without being named or formally defined
- ABSENT = no chapter covers this item

---

## CHO -- Choice (9 items)

| ID | Concept | Tier | Canonical Ch | Other Ch | Coverage | Redundancy |
|----|---------|------|-------------|----------|----------|------------|
| PRIM-CHO001 | Scarcity reasoning | C | Ch 1 | Ch 2, 21 | FULL | EXPECTED (micro and macro contexts) |
| PRIM-CHO002 | Opportunity cost reasoning | C | Ch 1 | Ch 2, 19 | FULL | EXPECTED (personal and trade contexts) |
| PRIM-CHO003 | Marginal analysis | C | Ch 2 | Ch 6, 7, 8 | FULL | COMPRESSION-TARGET (Ch 6 utility, Ch 7 costs, Ch 8 profit max are applications) |
| PRIM-CHO004 | Incentive reasoning | C | Ch 1 | Ch 3, 10, 12 | FULL | COMPRESSION-TARGET (implicit throughout MKT) |
| PRIM-CHO005 | Trade and specialization reasoning | C | Ch 19 | Ch 34 | FULL | COMPRESSION-TARGET (Ch 34 duplicates Ch 19) |
| DEF-CHO001 | Production possibilities frontier | C | Ch 2 | Ch 19, 22 | FULL | EXPECTED (micro PPF in Ch 2, trade PPF in Ch 19, growth PPF in Ch 22) |
| DEF-CHO002 | Diminishing marginal returns | C | Ch 7 | Ch 2 | FULL | None (Ch 7 is the deep treatment; Ch 2 introduces the idea) |
| DEF-CHO003 | Comparative advantage | C | Ch 19 | Ch 34 | FULL | COMPRESSION-TARGET (Ch 34 duplicates) |
| AX-CHO001 | Rational self-interest | C | Ch 1 | -- | FULL | None |

**CHO Summary**: 9/9 items = FULL coverage. 0 ABSENT. No items require WRITE-ORIGINAL.

---

## MKT -- Markets (12 items)

| ID | Concept | Tier | Canonical Ch | Other Ch | Coverage | Redundancy |
|----|---------|------|-------------|----------|----------|------------|
| PRIM-MKT001 | Demand reasoning | C | Ch 3 | Ch 4, 14 | FULL | EXPECTED (goods market Ch 3, labor market Ch 4/14) |
| PRIM-MKT002 | Supply reasoning | C | Ch 3 | Ch 4, 14 | FULL | EXPECTED (goods market Ch 3, labor market Ch 4/14) |
| PRIM-MKT003 | Equilibrium reasoning | C | Ch 3 | Ch 4, 8, 14 | FULL | COMPRESSION-TARGET (applied in multiple chapters) |
| PRIM-MKT004 | Elasticity reasoning | C | Ch 5 | Ch 12, 32 | FULL | None (Ch 5 is definitive; other chapters apply it) |
| PRIM-MKT005 | Market structure reasoning | C | Ch 8 | Ch 9, 10, 11 | FULL | EXPECTED (one chapter per structure type is pedagogically justified) |
| DEF-MKT001 | Demand curve | C | Ch 3 | -- | FULL | None |
| DEF-MKT002 | Supply curve | C | Ch 3 | -- | FULL | None |
| DEF-MKT003 | Price ceiling and floor | C | Ch 3 | Ch 4 (min wage) | FULL | EXPECTED (generic in Ch 3, labor-specific in Ch 4) |
| DEF-MKT004 | Consumer and producer surplus | C | Ch 8 | Ch 3, 12, 19 | FULL | COMPRESSION-TARGET (Ch 8 is the full welfare analysis; others apply) |
| DEF-MKT005 | Deadweight loss | C | Ch 9 | Ch 12, 20 | FULL | EXPECTED (from monopoly Ch 9, from externality Ch 12, from tariff Ch 20) |
| DEF-MKT006 | Externality | C | Ch 12 | Ch 13 | FULL | EXPECTED (negative Ch 12, positive Ch 13 -- both needed for completeness) |
| DEF-MKT007 | Public good | E | Ch 13 | Ch 18 | FULL | None (Ch 13 defines; Ch 18 discusses government provision) |

**MKT Summary**: 12/12 items = FULL coverage. 0 ABSENT. No items require WRITE-ORIGINAL.

---

## MAC -- Macroeconomics (10 items)

| ID | Concept | Tier | Canonical Ch | Other Ch | Coverage | Redundancy |
|----|---------|------|-------------|----------|----------|------------|
| PRIM-MAC001 | GDP reasoning | C | Ch 21 | Ch 22, 25 | FULL | COMPRESSION-TARGET (Ch 22 applies GDP growth; Ch 25 overlaps) |
| PRIM-MAC002 | Unemployment reasoning | C | Ch 23 | Ch 26, 27 | FULL | None (Ch 23 is definitive; others reference) |
| PRIM-MAC003 | Inflation reasoning | C | Ch 24 | Ch 26, 30 | FULL | COMPRESSION-TARGET (Ch 24 is definitive; Ch 26 deploys via AD/AS) |
| PRIM-MAC004 | Price level reasoning | C | Ch 24 | Ch 26 | FULL | None (Ch 24 introduces; Ch 26 applies via AD/AS) |
| PRIM-MAC005 | Business cycle reasoning | C | Ch 26 | Ch 21, 27, 28, 32 | FULL | EXPECTED (introduced conceptually in Ch 21, formalized in Ch 26, applied in Ch 27/28/32) |
| DEF-MAC001 | Nominal vs. real values | C | Ch 21 | Ch 24 | FULL | EXPECTED (GDP context in Ch 21, inflation context in Ch 24) |
| DEF-MAC002 | Aggregate demand | C | Ch 26 | Ch 27, 32 | FULL | COMPRESSION-TARGET (Ch 27 Keynesian detail, Ch 32 fiscal policy application) |
| DEF-MAC003 | Aggregate supply | C | Ch 26 | Ch 22, 28 | FULL | COMPRESSION-TARGET (Ch 22 long-run growth, Ch 28 neoclassical emphasis) |
| DEF-MAC004 | Multiplier effect | E | Ch 27 | Ch 32 | FULL | None (Ch 27 develops the multiplier; Ch 32 applies it) |
| DEF-MAC005 | Trade balance | E | Ch 19 | Ch 25 | FULL | COMPRESSION-TARGET (Ch 25 duplicates macro trade perspective of Ch 19) |

**MAC Summary**: 10/10 items = FULL coverage. 0 ABSENT. No items require WRITE-ORIGINAL.

---

## MON -- Money & Banking (8 items)

| ID | Concept | Tier | Canonical Ch | Other Ch | Coverage | Redundancy |
|----|---------|------|-------------|----------|----------|------------|
| PRIM-MON001 | Money functions reasoning | C | Ch 29 | -- | FULL | None |
| PRIM-MON002 | Banking system reasoning | C | Ch 29 | Ch 30 | FULL | None (Ch 29 defines; Ch 30 discusses regulation) |
| PRIM-MON003 | Interest rate reasoning | C | Ch 30 | Ch 4, 17, 31 | FULL | COMPRESSION-TARGET (Ch 4 and Ch 17 use interest rate informally; Ch 30 is definitive) |
| PRIM-MON004 | Money supply reasoning | C | Ch 29 | Ch 30 | FULL | None (Ch 29 defines via M1/M2; Ch 30 discusses Fed control) |
| DEF-MON001 | Fractional reserve banking | C | Ch 29 | Ch 30 | FULL | None |
| DEF-MON002 | Money multiplier | C | Ch 29 | -- | FULL | None |
| DEF-MON003 | Central bank operations | C | Ch 30 | -- | FULL | None |
| DEF-MON004 | Exchange rate | E | Ch 31 | Ch 25 | FULL | None (Ch 31 is definitive; Ch 25 touches on it) |

**MON Summary**: 8/8 items = FULL coverage. 0 ABSENT. No items require WRITE-ORIGINAL.

---

## POL -- Policy (8 items)

| ID | Concept | Tier | Canonical Ch | Other Ch | Coverage | Redundancy |
|----|---------|------|-------------|----------|----------|------------|
| PRIM-POL001 | Market failure correction reasoning | C | Ch 12 | Ch 11, 13, 18 | FULL | EXPECTED (externality correction Ch 12, antitrust Ch 11, public goods Ch 13, general Ch 18) |
| PRIM-POL002 | Fiscal policy reasoning | C | Ch 32 | Ch 27, 33 | FULL | COMPRESSION-TARGET (Ch 27 Keynesian fiscal; Ch 33 comparative) |
| PRIM-POL003 | Monetary policy reasoning | C | Ch 30 | Ch 33 | FULL | None (Ch 30 is definitive) |
| DEF-POL001 | Government budget and deficit | C | Ch 32 | Ch 18, 33 | FULL | COMPRESSION-TARGET (Ch 18 and Ch 33 discuss partially) |
| DEF-POL002 | Tax incidence | C | Ch 12 | Ch 5, 18 | PARTIAL | None |
| DEF-POL003 | Trade policy | E | Ch 20 | Ch 34 | FULL | COMPRESSION-TARGET (Ch 34 duplicates) |
| AX-POL001 | Efficiency-equity tradeoff | C | Ch 15 | Ch 1, 18, 32 | IMPLICIT | None |
| AX-POL002 | No free lunch in policy | C | Ch 1 | Ch 12, 15, 32 | IMPLICIT | None |

**POL Summary**: 6/8 items = FULL, 1 PARTIAL, 2 IMPLICIT. 0 ABSENT. No items require WRITE-ORIGINAL.

### POL Coverage Notes

- **DEF-POL002 (Tax incidence)**: PARTIAL. OpenStax Ch 12 discusses tax incidence in the externality context but does not give the full elasticity-based incidence analysis at the depth the taxonomy specifies. Ch 5 (Elasticity) discusses revenue effects but not formal incidence. The lean text must strengthen this to FULL.
- **AX-POL001 (Efficiency-equity tradeoff)**: IMPLICIT. The tradeoff is invoked throughout the textbook but never stated as an explicit axiom. OpenStax treats it as assumed background, not a named principle. The lean text must make it explicit.
- **AX-POL002 (No free lunch in policy)**: IMPLICIT. Same situation: the principle is deployed throughout but never named or formalized. Mankiw's "Ten Principles" (SRC-GLB002) state it explicitly; OpenStax does not. The lean text must make it explicit.

---

## Composition Patterns (7 CPs)

| ID | Name | Canonical Chapters | Coverage |
|----|------|--------------------|----------|
| CP-001 | How Prices Allocate Scarce Resources | Ch 1 + Ch 3 | FULL (reasoning chain is fully supported) |
| CP-002 | Why Trade Makes Both Sides Better Off | Ch 19 + Ch 3 + Ch 21 | FULL |
| CP-003 | Tax Incidence and Deadweight Loss | Ch 5 + Ch 12 | PARTIAL (see DEF-POL002 note) |
| CP-004 | How the Fed Fights Recession | Ch 29 + Ch 30 + Ch 26 | FULL |
| CP-005 | The Minimum Wage Debate | Ch 4 + Ch 3 + Ch 15 | FULL |
| CP-006 | Inflation and the Cost of Living | Ch 24 + Ch 29 | FULL |
| CP-007 | Correcting Pollution Externalities | Ch 12 + Ch 13 | FULL |

---

## Aggregate Coverage Summary

| Coverage Level | Count | Percentage | Items |
|----------------|-------|------------|-------|
| FULL | 44 | 93.6% | All items except 3 below |
| PARTIAL | 1 | 2.1% | DEF-POL002 |
| IMPLICIT | 2 | 4.3% | AX-POL001, AX-POL002 |
| ABSENT | 0 | 0.0% | --- |
| **Total** | **47** | **100%** | |

### Backtracking Check (Quality Gate QG2-5)

ABSENT + UNCERTAIN = 0 items = 0% of 47 total items.

Threshold: 20%. Result: **PASS** (well below threshold). No backtracking to Phase 1 required.

### WRITE-ORIGINAL Items

No items flagged for WRITE-ORIGINAL. All 47 taxonomy items have at least IMPLICIT source coverage.

However, 3 items require **strengthening** in the lean text:
1. **DEF-POL002** (Tax incidence): Upgrade from PARTIAL to FULL by providing the complete elasticity-based incidence analysis
2. **AX-POL001** (Efficiency-equity tradeoff): Make explicit what OpenStax leaves implicit
3. **AX-POL002** (No free lunch in policy): Make explicit what OpenStax leaves implicit

---

## Redundancy Resolution

For every item with 2+ defining sections, the canonical section was designated in the table above. The following items are flagged as COMPRESSION-TARGET (where the non-canonical treatment should be merged into the canonical):

| Item | Canonical | Compress From | Action for Phase 3 |
|------|-----------|---------------|---------------------|
| PRIM-CHO003 | Ch 2 | Ch 6 (utility), Ch 7 (costs), Ch 8 (profit max) | Merge applications into deployment examples |
| PRIM-CHO004 | Ch 1 | Ch 3, 10, 12 | Remove re-introductions; reference back to Ch 1 |
| PRIM-CHO005 | Ch 19 | Ch 34 | Drop Ch 34 content (duplicate) |
| DEF-CHO003 | Ch 19 | Ch 34 | Drop Ch 34 content (duplicate) |
| PRIM-MKT003 | Ch 3 | Ch 4, 8, 14 | Applications remain but do not re-define equilibrium |
| DEF-MKT004 | Ch 8 | Ch 3, 12, 19 | Keep Ch 8 as welfare analysis; others reference |
| PRIM-MAC001 | Ch 21 | Ch 22, 25 | Ch 22 applications stay; Ch 25 content merged |
| PRIM-MAC003 | Ch 24 | Ch 26, 30 | Ch 26 deploys via AD/AS; Ch 30 discusses monetary cause |
| DEF-MAC002 | Ch 26 | Ch 27, 32 | Ch 27 multiplier stays; Ch 32 fiscal application stays |
| DEF-MAC003 | Ch 26 | Ch 22, 28 | Ch 22 growth context; Ch 28 neoclassical emphasis |
| DEF-MAC005 | Ch 19 | Ch 25 | Merge Ch 25 unique content into Ch 19 treatment |
| PRIM-MON003 | Ch 30 | Ch 4, 17, 31 | Remove informal pre-introductions |
| PRIM-POL002 | Ch 32 | Ch 27, 33 | Ch 27 multiplier link stays; Ch 33 examples compress |
| DEF-POL001 | Ch 32 | Ch 18, 33 | Merge partial treatments |
| DEF-POL003 | Ch 20 | Ch 34 | Drop Ch 34 content (duplicate) |
