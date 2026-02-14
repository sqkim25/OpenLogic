# 01-OPENSTAX-ECON-MAP v0.1

> Phase 2 Source Map | Source: OpenStax *Principles of Economics* 3e (SRC-GLB001)
> Taxonomy: 5 domains, 47 items, 7 CPs (see `../taxonomy/CONVENTIONS.md`)

---

## Methodology

Each OpenStax chapter is tagged with:
- **Domain**: Primary taxonomy domain(s)
- **Introduces**: Taxonomy items this chapter defines (FULL coverage)
- **References**: Taxonomy items used but not defined here (IMPLICIT)
- **Compression signal**: CORE-DEF | STEPPING-STONE | PEDAGOGICAL | TANGENTIAL
- **Action signal**: ADAPT (rewrite at non-majors depth) | REWRITE (compress or restructure significantly)

Chapters are grouped by the textbook's natural micro/macro division, then mapped onto the taxonomy's topological order (CHO --> MKT --> MON --> MAC --> POL).

---

## Part I: Foundations and Choice (Ch 1--2)

### Ch 1: Welcome to Economics!

| Field | Value |
|-------|-------|
| **Domain** | CHO |
| **Introduces** | PRIM-CHO001 (scarcity reasoning), PRIM-CHO002 (opportunity cost reasoning), PRIM-CHO004 (incentive reasoning), AX-CHO001 (rational self-interest) |
| **References** | PRIM-CHO003 (marginal analysis -- mentioned but not developed) |
| **Compression** | CORE-DEF |
| **Action** | ADAPT -- foundational chapter; compress narrative, keep all primitives |
| **Notes** | The "three key questions" (what, how, for whom) are pedagogical framing, not taxonomy items. Division of economics into micro/macro is organizational, not conceptual. |

### Ch 2: Choice in a World of Scarcity

| Field | Value |
|-------|-------|
| **Domain** | CHO |
| **Introduces** | PRIM-CHO003 (marginal analysis), DEF-CHO001 (PPF), DEF-CHO002 (diminishing marginal returns -- introduced via production) |
| **References** | PRIM-CHO001, PRIM-CHO002, PRIM-CHO004 |
| **Compression** | CORE-DEF |
| **Action** | ADAPT -- core visualization chapter; the PPF and marginal analysis are fully developed here |
| **Notes** | Budget constraint section is a consumer-side application of scarcity; subsume under PRIM-CHO001 deployment. Utility maximization is a STEPPING-STONE for marginal analysis. |

---

## Part II: Markets (Ch 3--13)

### Ch 3: Demand and Supply

| Field | Value |
|-------|-------|
| **Domain** | MKT |
| **Introduces** | PRIM-MKT001 (demand reasoning), PRIM-MKT002 (supply reasoning), PRIM-MKT003 (equilibrium reasoning), DEF-MKT001 (demand curve), DEF-MKT002 (supply curve), DEF-MKT003 (price ceiling and floor) |
| **References** | PRIM-CHO003, PRIM-CHO004, AX-CHO001, DEF-CHO002 |
| **Compression** | CORE-DEF |
| **Action** | ADAPT -- the single most important chapter for MKT domain; preserve all six items |
| **Notes** | Price controls (ceiling/floor) introduced at the end. Shift vs. movement distinction is critical pedagogical content that maps to PRIM-MKT001/002. |

### Ch 4: Labor and Financial Markets

| Field | Value |
|-------|-------|
| **Domain** | MKT |
| **Introduces** | (none new -- applies S/D to labor and financial markets) |
| **References** | PRIM-MKT001, PRIM-MKT002, PRIM-MKT003, DEF-MKT003 (minimum wage as price floor), PRIM-MON003 (interest rate -- used informally) |
| **Compression** | STEPPING-STONE |
| **Action** | REWRITE -- merge labor market application into Ch 3 framework; financial markets content absorbed into MON domain |
| **Notes** | Minimum wage discussion is a deployment of DEF-MKT003 + CP-005. Interest rate discussion foreshadows MON but does not formally introduce it. |

### Ch 5: Elasticity

| Field | Value |
|-------|-------|
| **Domain** | MKT |
| **Introduces** | PRIM-MKT004 (elasticity reasoning) |
| **References** | PRIM-MKT001, PRIM-MKT002, PRIM-MKT003 |
| **Compression** | CORE-DEF |
| **Action** | ADAPT -- focused chapter; elasticity is a threshold concept. Compress the taxonomy of elasticity types (cross-price, income) to essentials |
| **Notes** | Income elasticity and cross-price elasticity are sub-cases of PRIM-MKT004; do not need separate taxonomy items. |

### Ch 6: Consumer Choices (Utility)

| Field | Value |
|-------|-------|
| **Domain** | CHO |
| **Introduces** | (none new) |
| **References** | PRIM-CHO003 (marginal analysis -- applied as marginal utility), AX-CHO001 (rational self-interest), PRIM-CHO001 (scarcity via budget constraint) |
| **Compression** | PEDAGOGICAL |
| **Action** | REWRITE -- utility theory is a formalization of marginal analysis (PRIM-CHO003). For non-majors, the marginal utility framework is a deployment exercise, not a new primitive. Compress heavily. |
| **Notes** | Marginal utility = marginal benefit in consumer context. Budget constraint = scarcity. The "rule" MU/P equalized across goods is an application of PRIM-CHO003. |

### Ch 7: Production, Costs, and Industry Structure

| Field | Value |
|-------|-------|
| **Domain** | CHO, MKT |
| **Introduces** | (none new -- deepens DEF-CHO002 into cost curves) |
| **References** | DEF-CHO002 (diminishing marginal returns), PRIM-CHO003 (marginal analysis -- MC, ATC, AVC), PRIM-MKT005 (market structure -- foreshadowed) |
| **Compression** | STEPPING-STONE |
| **Action** | REWRITE -- cost curve mechanics are a stepping stone for market structure. For non-majors: keep the MC-rising-from-DMR connection, drop detailed curve construction. |
| **Notes** | Long-run average cost (economies of scale) feeds into PRIM-MKT005 but does not need a separate item. |

### Ch 8: Perfect Competition

| Field | Value |
|-------|-------|
| **Domain** | MKT |
| **Introduces** | PRIM-MKT005 (market structure reasoning -- perfect competition as benchmark) |
| **References** | PRIM-MKT003 (equilibrium), PRIM-CHO003 (marginal analysis: P = MC), DEF-MKT004 (consumer and producer surplus -- efficiency of competitive market) |
| **Compression** | CORE-DEF |
| **Action** | ADAPT -- perfect competition establishes the efficiency benchmark. The P = MC condition and zero economic profit in long run are the core content. |
| **Notes** | DEF-MKT004 (surplus) gets its fullest treatment here (total surplus maximized at competitive equilibrium). |

### Ch 9: Monopoly

| Field | Value |
|-------|-------|
| **Domain** | MKT |
| **Introduces** | (none new -- monopoly is a case of PRIM-MKT005) |
| **References** | PRIM-MKT005 (market structure: N=1), DEF-MKT005 (deadweight loss from monopoly), PRIM-CHO003 (MR = MC decision) |
| **Compression** | CORE-DEF |
| **Action** | ADAPT -- monopoly is the key departure from competitive benchmark; DWL from monopoly is the micro rationale for antitrust (PRIM-POL001) |
| **Notes** | Introduces DEF-MKT005 (deadweight loss) in the monopoly context. Canonical section for DWL from market power. |

### Ch 10: Monopolistic Competition and Oligopoly

| Field | Value |
|-------|-------|
| **Domain** | MKT |
| **Introduces** | (none new -- completes PRIM-MKT005 coverage) |
| **References** | PRIM-MKT005 (market structure: monopolistic competition, oligopoly), PRIM-CHO004 (incentive reasoning: strategic behavior in oligopoly) |
| **Compression** | STEPPING-STONE |
| **Action** | REWRITE -- compress oligopoly game theory to essential intuition. Non-majors need the classification, not the formal models. |
| **Notes** | Prisoner's dilemma / game theory is TANGENTIAL for the non-majors taxonomy. |

### Ch 11: Monopoly and Antitrust Policy

| Field | Value |
|-------|-------|
| **Domain** | POL, MKT |
| **Introduces** | (none new -- applies PRIM-POL001 to market power) |
| **References** | PRIM-POL001 (market failure correction: antitrust as correction for monopoly), PRIM-MKT005 (market structure), DEF-MKT005 (deadweight loss) |
| **Compression** | STEPPING-STONE |
| **Action** | REWRITE -- merge antitrust into PRIM-POL001 market failure correction discussion. Compress regulatory history. |
| **Notes** | Historical content (Sherman Act, Clayton Act) is PEDAGOGICAL context for PRIM-POL001 deployment. |

### Ch 12: Environmental Protection and Negative Externalities

| Field | Value |
|-------|-------|
| **Domain** | MKT, POL |
| **Introduces** | DEF-MKT006 (externality -- negative), DEF-MKT005 (deadweight loss from externality) |
| **References** | PRIM-MKT003 (equilibrium: social vs. private), PRIM-POL001 (market failure correction: Pigouvian tax, cap-and-trade, regulation), DEF-POL002 (tax incidence -- applied to Pigouvian tax), PRIM-CHO004 (incentive reasoning) |
| **Compression** | CORE-DEF |
| **Action** | ADAPT -- canonical source for DEF-MKT006 (negative externality) and CP-007 deployment |
| **Notes** | Coase theorem mentioned; treat as PEDAGOGICAL enrichment, not a separate taxonomy item. Property rights solutions are part of PRIM-POL001. |

### Ch 13: Positive Externalities and Public Goods

| Field | Value |
|-------|-------|
| **Domain** | MKT, POL |
| **Introduces** | DEF-MKT007 (public good), DEF-MKT006 (externality -- positive, completes the definition) |
| **References** | PRIM-MKT003, PRIM-POL001 (government provision as correction for public good undersupply), PRIM-CHO004 (free-rider problem via incentive reasoning) |
| **Compression** | CORE-DEF |
| **Action** | ADAPT -- canonical source for DEF-MKT007. Public goods and positive externalities complete the market failure taxonomy. |
| **Notes** | Common resources (rivalrous but non-excludable) are a sub-case; do not need a separate item. |

---

## Part III: Labor, Inequality, and Information (Ch 14--18)

### Ch 14: Labor Markets and Income

| Field | Value |
|-------|-------|
| **Domain** | MKT |
| **Introduces** | (none new) |
| **References** | PRIM-MKT001, PRIM-MKT002, PRIM-MKT003 (S/D applied to labor), PRIM-CHO003 (marginal product of labor = demand for labor), DEF-CHO002 (diminishing marginal returns in labor market) |
| **Compression** | STEPPING-STONE |
| **Action** | REWRITE -- labor market analysis is a deployment of MKT primitives. Keep marginal productivity theory as application; compress detailed wage determination models. |
| **Notes** | Discrimination discussion is PEDAGOGICAL (important but not a distinct taxonomy reasoning move). |

### Ch 15: Poverty and Economic Inequality

| Field | Value |
|-------|-------|
| **Domain** | POL |
| **Introduces** | (none new) |
| **References** | AX-POL001 (efficiency-equity tradeoff), PRIM-POL002 (fiscal policy: redistribution), AX-POL002 (no free lunch: redistribution has costs) |
| **Compression** | PEDAGOGICAL |
| **Action** | REWRITE -- poverty/inequality is a deployment of AX-POL001, not a separate primitive. UNK-GLB003 in the taxonomy flags this as an open decision. For the stress test, treat as application context. |
| **Notes** | Gini coefficient, poverty line definitions are measurement tools, not reasoning moves. |

### Ch 16: Information, Risk, and Insurance

| Field | Value |
|-------|-------|
| **Domain** | MKT |
| **Introduces** | (none new) |
| **References** | PRIM-MKT005 (information asymmetry as market imperfection), PRIM-CHO004 (incentive reasoning: moral hazard, adverse selection), PRIM-POL001 (market failure from information problems) |
| **Compression** | TANGENTIAL |
| **Action** | REWRITE -- information economics is an extension area (see CONVENTIONS.md Section 6). Compress to essential intuition: information asymmetry as a type of market failure. |
| **Notes** | Moral hazard and adverse selection are applications of incentive reasoning + market failure. Not separate taxonomy items at the non-majors level. |

### Ch 17: Financial Markets

| Field | Value |
|-------|-------|
| **Domain** | MON |
| **Introduces** | (none new -- foreshadows MON concepts) |
| **References** | PRIM-MON003 (interest rate reasoning -- bond pricing), PRIM-MON001 (money functions -- financial assets as stores of value) |
| **Compression** | STEPPING-STONE |
| **Action** | REWRITE -- financial markets content supports MON domain. Bond pricing and stock market basics are deployment exercises for PRIM-MON003. Merge relevant content into MON chapter. |
| **Notes** | Personal finance advice is PEDAGOGICAL, not taxonomy content. |

### Ch 18: Public Economy

| Field | Value |
|-------|-------|
| **Domain** | POL |
| **Introduces** | (none new) |
| **References** | DEF-POL001 (government budget and deficit), DEF-POL002 (tax incidence), PRIM-POL001 (market failure correction: public goods provision), AX-POL001 (efficiency-equity tradeoff), AX-POL002 (no free lunch) |
| **Compression** | STEPPING-STONE |
| **Action** | REWRITE -- public choice and government spending analysis is a deployment of POL primitives. Compress into POL chapter. Voting theory is TANGENTIAL for the taxonomy. |
| **Notes** | Government failure / rent-seeking supports ASM-POL002 but does not need a separate item. |

---

## Part IV: International Trade (Ch 19--20)

### Ch 19: International Trade and Capital Flows

| Field | Value |
|-------|-------|
| **Domain** | CHO, MAC |
| **Introduces** | DEF-CHO003 (comparative advantage -- canonical quantitative treatment), PRIM-CHO005 (trade and specialization reasoning), DEF-MAC005 (trade balance) |
| **References** | PRIM-CHO002 (opportunity cost), DEF-CHO001 (PPF -- expanded to trade context), PRIM-MAC001 (GDP: NX component) |
| **Compression** | CORE-DEF |
| **Action** | ADAPT -- canonical source for comparative advantage calculations and trade balance. Key chapter for CP-002. |
| **Notes** | Intra-industry trade is TANGENTIAL for the non-majors taxonomy. |

### Ch 20: Globalization and Protectionism

| Field | Value |
|-------|-------|
| **Domain** | POL |
| **Introduces** | DEF-POL003 (trade policy -- tariffs, quotas, trade agreements) |
| **References** | DEF-CHO003 (comparative advantage), DEF-MKT005 (deadweight loss from tariffs), PRIM-MKT003 (equilibrium with trade restrictions), AX-POL001, AX-POL002 |
| **Compression** | CORE-DEF |
| **Action** | ADAPT -- canonical source for DEF-POL003. Compress historical/institutional detail; keep the tariff welfare analysis. |
| **Notes** | WTO, NAFTA/USMCA history is PEDAGOGICAL context. |

---

## Part V: Macroeconomics (Ch 21--28)

### Ch 21: The Macroeconomic Perspective

| Field | Value |
|-------|-------|
| **Domain** | MAC |
| **Introduces** | PRIM-MAC001 (GDP reasoning), DEF-MAC001 (nominal vs. real values) |
| **References** | PRIM-CHO001 (scarcity at national level), DEF-CHO001 (PPF -- national productive capacity) |
| **Compression** | CORE-DEF |
| **Action** | ADAPT -- canonical introduction to GDP measurement. The expenditure approach (C + I + G + NX) and real vs. nominal distinction are core. |
| **Notes** | GDP limitations discussion (does not count household work, leisure, environmental quality) is PEDAGOGICAL but important for non-majors. |

### Ch 22: Economic Growth

| Field | Value |
|-------|-------|
| **Domain** | MAC |
| **Introduces** | (none new -- economic growth is LRAS shift / PPF expansion) |
| **References** | PRIM-MAC001 (GDP growth), DEF-CHO001 (PPF outward shift), DEF-MAC003 (aggregate supply -- long-run growth shifts LRAS right) |
| **Compression** | STEPPING-STONE |
| **Action** | REWRITE -- growth is a deployment of MAC001 and AS reasoning. Compress Solow model to intuition: capital accumulation + technology + human capital drive long-run growth. |
| **Notes** | Rule of 70, convergence debate are PEDAGOGICAL. |

### Ch 23: Unemployment

| Field | Value |
|-------|-------|
| **Domain** | MAC |
| **Introduces** | PRIM-MAC002 (unemployment reasoning) |
| **References** | PRIM-MAC001 (GDP -- Okun's law connects unemployment to GDP gap), PRIM-MAC005 (business cycle: cyclical unemployment) |
| **Compression** | CORE-DEF |
| **Action** | ADAPT -- canonical source for unemployment typology (frictional, structural, cyclical) and natural rate. |
| **Notes** | Labor force participation rate and underemployment are measurement refinements, not separate primitives. |

### Ch 24: Inflation

| Field | Value |
|-------|-------|
| **Domain** | MAC |
| **Introduces** | PRIM-MAC003 (inflation reasoning), PRIM-MAC004 (price level reasoning) |
| **References** | PRIM-MAC001 (nominal vs. real GDP), DEF-MAC001 (nominal vs. real values -- Fisher equation), PRIM-MON004 (money supply -- quantity theory foreshadowed) |
| **Compression** | CORE-DEF |
| **Action** | ADAPT -- canonical source for CPI, demand-pull vs. cost-push, and redistribution effects. Key chapter for CP-006. |
| **Notes** | Hyperinflation examples are PEDAGOGICAL hooks. Indexation is a practical application, not a primitive. |

### Ch 25: The International Trade and Capital Flows

| Field | Value |
|-------|-------|
| **Domain** | MAC |
| **Introduces** | (none new -- overlaps with Ch 19) |
| **References** | DEF-MAC005 (trade balance), PRIM-MAC001 (GDP: NX component), DEF-CHO003 (comparative advantage) |
| **Compression** | TANGENTIAL |
| **Action** | REWRITE -- significant overlap with Ch 19. Merge unique macro-perspective content (national savings identity: S - I = NX) into the trade balance treatment. |
| **Notes** | This chapter appears to duplicate Ch 19 from the macro perspective. Canonical content already captured. |

### Ch 26: The Aggregate Demand/Aggregate Supply Model

| Field | Value |
|-------|-------|
| **Domain** | MAC |
| **Introduces** | DEF-MAC002 (aggregate demand), DEF-MAC003 (aggregate supply), PRIM-MAC005 (business cycle reasoning -- formalized via AD/AS) |
| **References** | PRIM-MKT001, PRIM-MKT002 (micro S/D as foundation), DEF-MKT001, DEF-MKT002 (curve concepts), PRIM-MAC001, PRIM-MAC003, PRIM-MAC004 |
| **Compression** | CORE-DEF |
| **Action** | ADAPT -- canonical source for AD/AS model. The central analytical framework of macroeconomics for non-majors. |
| **Notes** | SRAS vs. LRAS distinction is essential. Recessionary gap and inflationary gap are applications of PRIM-MAC005 via AD/AS. |

### Ch 27: The Keynesian Perspective

| Field | Value |
|-------|-------|
| **Domain** | MAC, POL |
| **Introduces** | DEF-MAC004 (multiplier effect) |
| **References** | DEF-MAC002 (aggregate demand), PRIM-POL002 (fiscal policy reasoning), PRIM-CHO003 (marginal propensity to consume is a marginal concept) |
| **Compression** | CORE-DEF |
| **Action** | ADAPT -- canonical source for the multiplier. Compress Keynesian cross diagram to essential multiplier reasoning. The MPC-to-multiplier chain is the core content. |
| **Notes** | Full Keynesian cross model is STEPPING-STONE; the multiplier concept (DEF-MAC004) is the extractable primitive. Sticky wages/prices are assumptions supporting SRAS, not separate items. |

### Ch 28: The Neoclassical Perspective

| Field | Value |
|-------|-------|
| **Domain** | MAC |
| **Introduces** | (none new) |
| **References** | DEF-MAC003 (aggregate supply -- neoclassical emphasis on LRAS), PRIM-MAC005 (business cycle: self-correcting economy), PRIM-MAC001 (potential GDP) |
| **Compression** | PEDAGOGICAL |
| **Action** | REWRITE -- the Keynesian vs. neoclassical debate is a PEDAGOGICAL framing. The taxonomy captures both perspectives: Keynesian emphasis on AD/multiplier (DEF-MAC002, DEF-MAC004) and neoclassical emphasis on LRAS (DEF-MAC003). For non-majors, compress to the essential insight: short-run AD matters (Keynesian), long-run AS matters (neoclassical). |
| **Notes** | Say's Law, rational expectations are TANGENTIAL for non-majors. |

---

## Part VI: Money, Banking, and Monetary Policy (Ch 29--31)

### Ch 29: Money and Banking

| Field | Value |
|-------|-------|
| **Domain** | MON |
| **Introduces** | PRIM-MON001 (money functions reasoning), PRIM-MON002 (banking system reasoning), DEF-MON001 (fractional reserve banking), DEF-MON002 (money multiplier), PRIM-MON004 (money supply reasoning) |
| **References** | PRIM-CHO001 (scarcity of loanable funds), AX-CHO001 (banks maximize profit) |
| **Compression** | CORE-DEF |
| **Action** | ADAPT -- canonical source for all core MON items except interest rate and central bank operations. The most item-dense chapter in the mapping. |
| **Notes** | History of money (barter, commodity money, fiat money) is PEDAGOGICAL context for PRIM-MON001. M1/M2 definitions are measurement detail. |

### Ch 30: Monetary Policy and Bank Regulation

| Field | Value |
|-------|-------|
| **Domain** | MON, POL |
| **Introduces** | DEF-MON003 (central bank operations), PRIM-MON003 (interest rate reasoning), PRIM-POL003 (monetary policy reasoning) |
| **References** | PRIM-MON004 (money supply), DEF-MON002 (money multiplier), DEF-MAC002 (aggregate demand -- monetary transmission), PRIM-MAC003 (inflation target) |
| **Compression** | CORE-DEF |
| **Action** | ADAPT -- canonical source for central bank operations and monetary policy deployment. Bank regulation (FDIC, capital requirements) is STEPPING-STONE context for DEF-MON001. |
| **Notes** | Quantitative easing is a modern extension of DEF-MON003 (open-market operations at scale). |

### Ch 31: Exchange Rates and International Capital Flows

| Field | Value |
|-------|-------|
| **Domain** | MON |
| **Introduces** | DEF-MON004 (exchange rate) |
| **References** | PRIM-MON003 (interest rate differentials drive capital flows), DEF-MAC005 (trade balance), PRIM-MAC004 (price level -- purchasing power parity) |
| **Compression** | CORE-DEF |
| **Action** | ADAPT -- canonical source for DEF-MON004. Compress institutional detail (fixed vs. floating regimes) to essentials. |
| **Notes** | DEF-MON004 is Enrichment tier; this chapter can be made optional. |

---

## Part VII: Fiscal Policy and the Role of Government (Ch 32--34)

### Ch 32: Government Budgets and Fiscal Policy

| Field | Value |
|-------|-------|
| **Domain** | POL |
| **Introduces** | PRIM-POL002 (fiscal policy reasoning), DEF-POL001 (government budget and deficit) |
| **References** | DEF-MAC002 (AD shifts from fiscal policy), PRIM-MAC005 (business cycle: countercyclical fiscal policy), DEF-MAC004 (multiplier effect), AX-POL002 (no free lunch: deficit spending has costs) |
| **Compression** | CORE-DEF |
| **Action** | ADAPT -- canonical source for fiscal policy and government budget. Compress deficit/debt mechanics to essential reasoning. |
| **Notes** | Automatic stabilizers (unemployment insurance, progressive taxation) are applications of PRIM-POL002 + PRIM-CHO004 (incentive reasoning). |

### Ch 33: Macroeconomic Policy Around the World

| Field | Value |
|-------|-------|
| **Domain** | POL, MAC |
| **Introduces** | (none new) |
| **References** | PRIM-POL002, PRIM-POL003, PRIM-MAC005, DEF-MAC002, DEF-MAC003, AX-POL001, AX-POL002 |
| **Compression** | PEDAGOGICAL |
| **Action** | REWRITE -- international policy comparisons are deployment exercises for POL primitives. Compress to brief case studies illustrating POL reasoning in different contexts. |
| **Notes** | Country-specific details (EU, Japan, China) are PEDAGOGICAL, not taxonomy items. |

### Ch 34: International Trade

| Field | Value |
|-------|-------|
| **Domain** | CHO, POL |
| **Introduces** | (none new -- overlaps significantly with Ch 19 and Ch 20) |
| **References** | DEF-CHO003 (comparative advantage), DEF-POL003 (trade policy), DEF-MKT005 (DWL from tariffs), AX-POL002 |
| **Compression** | TANGENTIAL |
| **Action** | REWRITE -- near-complete overlap with Ch 19 (trade theory) and Ch 20 (trade policy). Merge unique content; do not create a separate chapter. |
| **Notes** | This appears to be the textbook's second pass at trade from the macro section. All content is already mapped. |

---

## Summary Statistics

| Metric | Count |
|--------|-------|
| Total OpenStax chapters | 34 |
| Chapters classified CORE-DEF | 17 |
| Chapters classified STEPPING-STONE | 8 |
| Chapters classified PEDAGOGICAL | 4 |
| Chapters classified TANGENTIAL | 3 |
| Chapters not introducing any new items (pure deployment) | 2 (Ch 25, Ch 34 -- overlaps) |
| Action = ADAPT | 17 |
| Action = REWRITE | 17 |

### Compression Signal Distribution

| Signal | Chapters | Interpretation |
|--------|----------|----------------|
| CORE-DEF | 1, 2, 3, 5, 8, 9, 12, 13, 19, 20, 21, 23, 24, 26, 27, 29, 30 | These chapters introduce taxonomy items and must be preserved (adapted). |
| STEPPING-STONE | 4, 7, 10, 11, 14, 17, 18, 22 | These chapters bridge to core content; compress into the canonical treatment of the items they reference. |
| PEDAGOGICAL | 6, 15, 28, 33 | These chapters motivate or contextualize existing items; compress to hooks and examples. |
| TANGENTIAL | 16, 25, 34 | These chapters cover content outside the core taxonomy or duplicate other chapters. |

### Domain Coverage by Source Chapter

| Domain | Primary Chapters | Total Chapters Touching Domain |
|--------|-----------------|-------------------------------|
| CHO | 1, 2, 6, 19 | 10 |
| MKT | 3, 4, 5, 7, 8, 9, 10, 12, 13, 14 | 14 |
| MAC | 21, 22, 23, 24, 25, 26, 27, 28 | 12 |
| MON | 17, 29, 30, 31 | 5 |
| POL | 11, 15, 18, 20, 32, 33, 34 | 14 |
