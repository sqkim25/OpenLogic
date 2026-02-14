# DOMAIN-CHO v0.1

## 0. Sources & Assumptions

- SRC-CHO001: Becker, "The Economic Approach to Human Behavior," 1976 (foundational treatment of rational choice)
- SRC-CHO002: Ferraro & Taylor, "Do economists recognize an opportunity cost when they see one?" *American Economic Review*, 2005 (even economists often misidentify opportunity cost -- validates its status as a threshold concept)
- SRC-CHO003: Ricardo, *On the Principles of Political Economy and Taxation*, 1817 (original statement of comparative advantage)
- SRC-GLB001: OpenStax, *Principles of Economics*, 3rd ed., 2023, Ch. 1--2, 19, 33
- SRC-GLB002: Mankiw, *Principles of Economics*, 9th ed., 2021, Ch. 1--3
- SRC-GLB005: Davies & Mangan, "Threshold concepts and the integration of understanding in economics," *Studies in Higher Education*, 2007
- ASM-CHO001: Students enter with no prior formal economics. Everyday experience with personal decisions (budgeting, time management, career choices) provides the raw material. Justification: the non-majors population has no assumed economics background; personal decision-making experience is universal.
- ASM-CHO002: Rationality is presented as a useful modeling assumption, not a description of how people always behave. Behavioral economics deviations are acknowledged as qualifications. Justification: non-majors need to understand the rational choice framework as a reasoning tool while recognizing its limits (ASM-GLB005).

## 1. Domain Intent

- **Governing question**: How do individuals and firms decide?
- **Scope**: The logic of decision-making under scarcity. This includes identifying tradeoffs, computing opportunity costs, reasoning at the margin, responding to incentives, and understanding gains from specialization and trade. CHO provides the decision layer: the foundational reasoning moves that every economic agent (consumer, worker, firm, government) deploys when making choices.
- **Non-goals**: How prices emerge from the interaction of many decision-makers (MKT). What happens when individual decisions aggregate to economy-wide outcomes (MAC). How the financial system channels decisions about saving and lending (MON). How governments intervene to change outcomes (POL).
- **Dissolution argument**: Choice logic answers HOW agents decide. Markets answer HOW prices coordinate those decisions into outcomes. You can analyze a single person's opportunity cost calculation (CHO) without any reference to supply curves, demand curves, or equilibrium prices (MKT). Robinson Crusoe alone on an island faces scarcity, opportunity costs, and marginal tradeoffs -- all CHO concepts -- despite having no market. Conversely, market reasoning assumes decision-making agents but does not define the decision logic itself; it takes the agent's preferences and constraints as inputs. Merging CHO into MKT would conflate the logic of individual choice with the mechanism of multi-agent coordination -- two cognitively distinct operations that students routinely fail to separate. Similarly, CHO cannot merge into POL because scarcity and tradeoffs exist with or without government; CHO is pre-political.
- **Threshold schema mapping**: Zero-sum --> Positive-sum. The foundational conceptual shift in CHO is recognizing that trade and specialization can make both parties better off -- the economy is not a fixed pie where one person's gain is another's loss. Students who fail to cross this threshold believe that imports "steal jobs" or that profits are "taken" from consumers. The threshold is crossed when students understand comparative advantage and voluntary exchange.

## 2. Prerequisites

CHO is the root domain. It imports nothing from MKT, MAC, MON, or POL. All other domains depend on CHO (directly or transitively). No DEP entries exist for this domain.

## 3. Primitives

- PRIM-CHO001: **Scarcity reasoning**
  - Reasoning move: Given a description of wants and available resources, determine whether the wants exceed the resources, and if so, identify the constraint that forces a tradeoff.
  - Description: The cognitive operation of recognizing that resources (time, money, raw materials, labor) are limited while human wants are unlimited. Scarcity is the foundational condition that makes economics necessary: without scarcity, there are no tradeoffs, no opportunity costs, and no need to choose. This primitive is not about poverty -- wealthy societies face scarcity too, because even abundant resources have alternative uses. The operation is: look at the wants, look at the resources, identify the gap, and recognize that choosing to satisfy one want means not satisfying another.
  - Semi-formal: Given a set of wants W = {w_1, w_2, ..., w_n} and a resource constraint R, scarcity exists iff the resources required to satisfy all wants exceed R: sum(cost(w_i)) > R. Scarcity forces choice: the agent must select a subset S of W such that sum(cost(w_i for w_i in S)) <= R. The remaining wants W - S are unmet.
  - Depends: none (foundational -- this is the root primitive of the entire taxonomy)
  - Ownership: CHO
  - Source: SRC-GLB001 (OpenStax Ch. 1), SRC-GLB002 (Mankiw Ch. 1)
  - Referenced by: MKT, MAC, POL
  - Tier: C
  - Real-world hook: You have 24 hours in a day but want to sleep, attend class, study, work part-time, exercise, and socialize. You cannot do all of them as much as you would like. That constraint -- finite hours, unlimited wants -- is scarcity. It is why you must choose, and why choosing has costs.

- PRIM-CHO002: **Opportunity cost reasoning**
  - Reasoning move: Given a decision between two or more alternatives, identify the value of the best forgone alternative to determine the true cost of the chosen option.
  - Description: The cognitive operation of recognizing that every choice has a hidden cost: not just the money spent, but the value of the next-best thing you gave up. Opportunity cost is the single most important reasoning move in economics because it transforms "how much does this cost?" from a simple price-tag question into a deeper analysis of tradeoffs. A student who goes to college does not just pay tuition -- they forgo the wages they could have earned. A city that builds a stadium does not just spend tax dollars -- it forgoes the school or hospital it could have built instead. Empirical research shows that even trained economists often misidentify opportunity cost in unfamiliar settings (SRC-CHO002), confirming its status as a genuine threshold concept.
  - Semi-formal: For decision-maker D choosing option A from set {A, B, C, ...}, the opportunity cost of A = value(best forgone alternative). If D chooses A, OC(A) = max(value(B), value(C), ...). The total economic cost of A = explicit cost(A) + OC(A).
  - Depends: PRIM-CHO001 (scarcity reasoning -- opportunity cost exists because resources are scarce; without scarcity, there are no tradeoffs)
  - Ownership: CHO
  - Source: SRC-GLB001 (OpenStax Ch. 1--2), SRC-GLB002 (Mankiw Ch. 1), SRC-CHO002 (Ferraro & Taylor 2005), SRC-GLB005 (Davies & Mangan 2007)
  - Referenced by: MKT, MAC, POL
  - Tier: C
  - Real-world hook: When you spend Friday evening studying for an exam instead of going to a concert, the opportunity cost of studying is the enjoyment of the concert. The cost of college is not just tuition -- it includes the four years of salary you did not earn. Recognizing opportunity cost changes how you evaluate every decision.

- PRIM-CHO003: **Marginal analysis**
  - Reasoning move: Given a decision about how much of something to do (not whether to do it), compare the additional benefit of one more unit to the additional cost of one more unit to determine the optimal quantity.
  - Description: The cognitive operation of thinking at the margin. Economic decisions are rarely all-or-nothing; they are about "how much?" Should a firm hire one more worker? Should you study one more hour? Should a factory produce one more widget? The answer depends on comparing marginal benefit (MB) to marginal cost (MC). If MB > MC, do more. If MB < MC, do less. The optimal quantity is where MB = MC. Marginal analysis is the operational core of rational decision-making because it provides a concrete stopping rule: keep going until the next unit costs more than it is worth. This moves reasoning away from averages and totals toward incremental thinking, which is the characteristic mode of economic reasoning.
  - Semi-formal: For activity X at quantity q: marginal benefit MB(q) = delta-TotalBenefit / delta-q (additional benefit from one more unit). Marginal cost MC(q) = delta-TotalCost / delta-q (additional cost from one more unit). Optimal decision: increase q while MB(q) > MC(q); stop when MB(q) = MC(q). If MB(q) < MC(q) at current q, reduce q.
  - Depends: PRIM-CHO001 (scarcity reasoning -- marginal analysis is needed because scarce resources force optimization)
  - Ownership: CHO
  - Source: SRC-GLB001 (OpenStax Ch. 2), SRC-GLB002 (Mankiw Ch. 1)
  - Referenced by: MKT, MAC, POL
  - Tier: C
  - Real-world hook: Should you study one more hour for tomorrow's exam? If the extra hour will raise your grade from B+ to A- (high marginal benefit) and you have nothing urgent to give up (low marginal cost), study more. If it will raise your grade from 98 to 99 (low marginal benefit) but you are exhausted (high marginal cost), stop. This is marginal analysis: deciding at the edge, not on averages.

- PRIM-CHO004: **Incentive reasoning**
  - Reasoning move: Given a change in costs, benefits, rules, or rewards facing a decision-maker, predict how the decision-maker's behavior will change in response to the altered incentives.
  - Description: The cognitive operation of tracing the behavioral consequences of changed incentives. People respond to incentives -- when the cost of something rises, people do less of it; when the reward for something rises, people do more of it. Incentive reasoning is the bridge between individual choice and systemic outcomes: by predicting how agents respond to changed conditions, you can anticipate the downstream effects of policies, price changes, regulations, and technological shifts. This primitive does not require that agents respond perfectly or immediately -- it requires only recognizing that systematic behavioral shifts follow from changed incentives. Incentive reasoning also reveals unintended consequences: a policy designed to produce outcome X may, through incentive effects, produce outcome Y instead.
  - Semi-formal: Given agent D with current behavior B and a change in the incentive structure delta-I (increase in cost, increase in reward, new rule, new information): predict B' (new behavior) by reasoning: if delta-I increases the cost of B, then B' involves less of B. If delta-I increases the reward for B, then B' involves more of B. Unintended consequences arise when delta-I creates incentives for behaviors the policy-maker did not anticipate.
  - Depends: PRIM-CHO001 (scarcity reasoning -- incentives matter because agents face constraints and must choose), PRIM-CHO003 (marginal analysis -- incentive changes shift MB or MC, causing agents to adjust at the margin)
  - Ownership: CHO
  - Source: SRC-GLB001 (OpenStax Ch. 1--2), SRC-GLB002 (Mankiw Ch. 1), SRC-GLB008 (Becker 1976)
  - Referenced by: MKT, POL
  - Tier: C
  - Real-world hook: When a city raises the cost of parking downtown, fewer people drive and more take the bus. When a company offers a year-end bonus for meeting sales targets, salespeople work harder in December. When the government subsidizes solar panels, more homeowners install them. In each case, changed incentives produce predictable behavioral shifts.

- PRIM-CHO005: **Trade and specialization reasoning**
  - Reasoning move: Given two agents (people, firms, or countries) with different abilities to produce goods, determine who should specialize in what and whether trade can make both better off, even if one agent is better at producing everything.
  - Description: The cognitive operation of recognizing that specialization and voluntary exchange can create mutual gains. This is one of the most counterintuitive results in economics: even if person A is better than person B at producing BOTH goods, both can still benefit by specializing in what they do relatively best (comparative advantage) and trading. The key insight is that trade is not zero-sum -- the total pie grows when agents specialize according to comparative advantage. This primitive bridges individual choice (each agent decides what to produce) and market outcomes (trade makes both better off), but the logic of specialization itself is a decision-making concept owned by CHO.
  - Semi-formal: Given agents A and B producing goods X and Y: absolute advantage -- A has absolute advantage in X if A can produce X with fewer resources than B. Comparative advantage -- A has comparative advantage in X if OC_A(X) < OC_B(X), i.e., A's opportunity cost of producing X is lower than B's. Trade is mutually beneficial when each agent specializes in the good where they have comparative advantage and trades for the other good. Both agents end up with more total goods than if each produced everything themselves.
  - Depends: PRIM-CHO002 (opportunity cost reasoning -- comparative advantage is defined in terms of opportunity cost)
  - Ownership: CHO
  - Source: SRC-GLB001 (OpenStax Ch. 19, 33), SRC-GLB002 (Mankiw Ch. 3), SRC-CHO003 (Ricardo 1817)
  - Referenced by: MKT, MAC
  - Tier: C
  - Real-world hook: A surgeon who is also a faster typist than her secretary still hires the secretary. Why? Because every hour the surgeon spends typing is an hour not spent performing surgery (high opportunity cost). The surgeon's comparative advantage is in surgery; the secretary's comparative advantage is in typing. Both are better off when each specializes. The same logic explains why countries trade: Bangladesh specializes in textiles not because it is better at making textiles than everything else, but because its opportunity cost of textile production is lower.

## 4. Definitions

- DEF-CHO001: **Production possibilities frontier (PPF)**
  - Reasoning move: Given a fixed set of resources and two possible outputs, construct or interpret the PPF curve to identify feasible, infeasible, and efficient production combinations, and to visualize opportunity cost as the slope of the frontier.
  - Description: The production possibilities frontier is the graphical representation of scarcity and tradeoffs. It shows all the combinations of two goods that an economy can produce using all available resources efficiently. Points on the frontier are efficient (all resources used). Points inside the frontier are feasible but inefficient (resources wasted). Points outside the frontier are infeasible (not enough resources). The slope of the PPF at any point represents the opportunity cost of producing one more unit of good X in terms of forgone units of good Y. A bowed-out PPF reflects increasing opportunity costs (resources are not equally suited to producing both goods). The PPF makes scarcity, tradeoffs, and opportunity cost visible in a single diagram.
  - Semi-formal: Given resources R and two goods X, Y: the PPF is the set of (x, y) pairs such that producing x units of X and y units of Y exactly exhausts R. For any point on the PPF, the opportunity cost of one more unit of X = |delta-Y / delta-X| (the slope). Inside the PPF: sum(resource use) < R. On the PPF: sum(resource use) = R. Outside the PPF: sum(resource use) > R (infeasible). Economic growth shifts the PPF outward.
  - Depends: PRIM-CHO001 (scarcity reasoning -- the PPF exists because resources are finite), PRIM-CHO002 (opportunity cost reasoning -- the PPF's slope is the visual representation of opportunity cost)
  - Ownership: CHO
  - Source: SRC-GLB001 (OpenStax Ch. 2), SRC-GLB002 (Mankiw Ch. 2)
  - Referenced by: MAC
  - Tier: C
  - Real-world hook: A country with a fixed labor force can produce military goods ("guns") or consumer goods ("butter"), but not unlimited amounts of both. The PPF shows the tradeoff: more tanks means fewer refrigerators. This is not a hypothetical -- it is exactly the tradeoff every national budget faces, made visible as a curve.

- DEF-CHO002: **Diminishing marginal returns**
  - Reasoning move: Given a production process where one input is being increased while others are held fixed, recognize that beyond some point, each additional unit of the variable input adds less additional output than the previous unit.
  - Description: Diminishing marginal returns is the observation that if you keep adding more of one input (say, workers) to a fixed amount of another input (say, a factory), eventually each additional worker contributes less than the one before. The first worker in an empty factory contributes enormously; the hundredth worker in a crowded factory may barely contribute at all. This is not because later workers are lazier -- it is because the fixed input (factory space, machines) becomes a bottleneck. Diminishing marginal returns is the production-side counterpart of marginal analysis: it explains why the marginal cost of production eventually rises, which in turn shapes supply curves (MKT).
  - Semi-formal: For a production function Q = f(L, K) where L (labor) is variable and K (capital) is fixed: marginal product of labor MPL = delta-Q / delta-L. Diminishing marginal returns: there exists a level L* such that for all L > L*, MPL is decreasing (each additional worker adds less output). Note: total output still increases; only the RATE of increase falls.
  - Depends: PRIM-CHO003 (marginal analysis -- diminishing marginal returns is about the marginal product declining)
  - Ownership: CHO
  - Source: SRC-GLB001 (OpenStax Ch. 7), SRC-GLB002 (Mankiw Ch. 13)
  - Referenced by: MKT
  - Tier: C
  - Real-world hook: Adding a second barista to a quiet coffee shop roughly doubles the output. Adding a tenth barista to the same small shop barely helps -- they are bumping into each other, sharing one espresso machine, and waiting for counter space. Each additional barista adds less than the last. The shop is experiencing diminishing marginal returns to labor.

- DEF-CHO003: **Comparative advantage**
  - Reasoning move: Given production data for two agents and two goods, compute each agent's opportunity cost of producing each good, then identify which agent has the lower opportunity cost for each good to determine who should specialize in what.
  - Description: Comparative advantage operationalizes trade and specialization reasoning into a concrete calculation. It is the quantitative version of PRIM-CHO005: instead of reasoning abstractly about "who should specialize," comparative advantage provides a step-by-step procedure. Compute the opportunity cost of each good for each agent, compare, and assign specialization to the agent with the lower opportunity cost. This definition resolves the common confusion between absolute advantage (who produces more?) and comparative advantage (who gives up less?) -- a confusion that is the source of most misconceptions about international trade.
  - Semi-formal: For agents A and B producing goods X and Y: OC_A(X) = units of Y forgone per unit of X produced by A. OC_B(X) = units of Y forgone per unit of X produced by B. A has comparative advantage in X iff OC_A(X) < OC_B(X). Necessarily, if A has CA in X, then B has CA in Y (since OC is reciprocal). Trade is mutually beneficial when each agent specializes in the good where they have CA and trades at any price between OC_A and OC_B.
  - Depends: PRIM-CHO002 (opportunity cost reasoning -- comparative advantage is defined by comparing opportunity costs), PRIM-CHO005 (trade and specialization reasoning -- comparative advantage is the formal criterion for optimal specialization)
  - Ownership: CHO
  - Source: SRC-GLB001 (OpenStax Ch. 19), SRC-GLB002 (Mankiw Ch. 3), SRC-CHO003 (Ricardo 1817)
  - Referenced by: MKT, MAC
  - Tier: C
  - Real-world hook: The US and Colombia both produce roses and computers. The US has an absolute advantage in both. But Colombia's opportunity cost of producing roses is low (it gives up few computers), while the US's opportunity cost of producing roses is high (it gives up many computers). Colombia has a comparative advantage in roses. That is why your Valentine's Day roses were likely grown in Colombia, even though the US could theoretically grow them too.

## 5. Axioms

- AX-CHO001: **Rational self-interest**
  - Statement: Economic agents (consumers, firms, governments) generally act to maximize their own perceived well-being, given their information and constraints.
  - Description: This is the foundational behavioral postulate of economic reasoning. It does NOT claim that people are selfish, perfectly informed, or always correct. It claims that people systematically respond to incentives in ways that (they believe) serve their interests. This assumption is what makes economic behavior predictable: if you know someone's incentives and constraints, you can predict their approximate behavior. Without this axiom, incentive reasoning (PRIM-CHO004) has no foundation, supply and demand have no behavioral basis, and policy analysis becomes impossible. The axiom is explicitly a simplification -- behavioral economics documents systematic deviations (cognitive biases, bounded rationality) -- but it remains the default model because it generates powerful predictions that are approximately correct across a wide range of contexts.
  - Depends: none (axiom -- taken as given)
  - Ownership: CHO
  - Source: SRC-GLB002 (Mankiw Ch. 1, Ten Principles), SRC-GLB008 (Becker 1976), SRC-GLB001 (OpenStax Ch. 1)
  - Referenced by: MKT, MAC, MON, POL
  - Tier: C
  - Normative: MUST (the entire taxonomy rests on agents responding to incentives; without this axiom, PRIM-CHO004, PRIM-MKT001, PRIM-MKT002, and all policy analysis lose their predictive foundation)
  - Real-world hook: When gas prices rise, people drive less, buy smaller cars, and take the bus. They are not being selfless or following orders -- they are rationally responding to changed costs. When wages for nurses rise in a shortage, more students choose nursing. Rational self-interest does not mean greed; it means predictable response to incentives.

## 6. Contested Concepts

The primary contested boundary for CHO is with MKT. Three concepts require explicit ownership resolution:

| Concept | CHO Version (Owner) | MKT Version (If Any) | Resolution |
|---------|---------------------|----------------------|------------|
| Demand | PRIM-CHO004 (incentive reasoning: people buy less when prices rise) is the individual behavior. | PRIM-MKT001 owns "demand reasoning" as the aggregated market behavior of all buyers expressed as a demand curve. | Clean split: CHO explains WHY an individual responds to price changes (incentive + marginal analysis). MKT explains HOW millions of individual decisions aggregate into a market demand curve. Boundary principle P1: individual decision logic is CHO; multi-agent price coordination is MKT. |
| Supply | CHO provides the marginal analysis (PRIM-CHO003) and diminishing returns (DEF-CHO002) that explain individual firm behavior. | PRIM-MKT002 owns "supply reasoning" as the aggregated market behavior of all sellers expressed as a supply curve. | Same split: CHO provides the decision logic; MKT provides the aggregation mechanism. |
| Comparative advantage | DEF-CHO003 owns the logic of optimal specialization (which agent should produce which good). | MKT uses comparative advantage when analyzing international trade patterns. | CHO owns the reasoning move; MKT and MAC reference it when analyzing trade outcomes. Boundary principle P4: one owner, many references. |

No contested concepts exist between CHO and MAC, MON, or POL. CHO's items are strictly about individual decision logic, which does not overlap with aggregate measurement (MAC), financial system mechanics (MON), or government intervention design (POL).

## 7. Real-World Hooks

| ID | Concept | Everyday Application |
|----|---------|---------------------|
| PRIM-CHO001 | Scarcity reasoning | You have $100 left after rent this week and need groceries, gas, and a textbook -- you cannot buy all three in full. Scarcity forces prioritization. |
| PRIM-CHO002 | Opportunity cost reasoning | The cost of college is not just tuition; it includes four years of forgone wages. |
| PRIM-CHO003 | Marginal analysis | "Should I study one more hour?" depends on comparing the marginal benefit (grade improvement) to the marginal cost (lost sleep, lost leisure). |
| PRIM-CHO004 | Incentive reasoning | When a city charges for plastic bags, people bring reusable bags. Changed incentive, changed behavior. |
| PRIM-CHO005 | Trade and specialization | A surgeon hires a typist even if the surgeon types faster, because the surgeon's time is better spent on surgery. |
| DEF-CHO001 | PPF | A country choosing between military spending and social programs visualizes the tradeoff on a PPF: more of one means less of the other. |
| DEF-CHO002 | Diminishing marginal returns | Adding a second barista doubles output; adding a tenth barely helps -- the shop is too crowded. |
| DEF-CHO003 | Comparative advantage | Your Valentine's Day roses come from Colombia because Colombia's opportunity cost of growing roses is lower than the US's. |
| AX-CHO001 | Rational self-interest | When gas prices rise, people drive less. Predictable response to incentives, not selfishness. |

## 8. Intra-Domain Dependency Graph

```
PRIM-CHO001 (Scarcity reasoning)
     |
     +---> PRIM-CHO002 (Opportunity cost reasoning)
     |          |
     |          +---> PRIM-CHO005 (Trade and specialization reasoning)
     |          |          |
     |          |          +---> DEF-CHO003 (Comparative advantage)
     |          |
     |          +---> DEF-CHO001 (PPF) [also depends on PRIM-CHO001]
     |
     +---> PRIM-CHO003 (Marginal analysis)
     |          |
     |          +---> PRIM-CHO004 (Incentive reasoning) [also depends on PRIM-CHO001]
     |          |
     |          +---> DEF-CHO002 (Diminishing marginal returns)
     |
     +---> AX-CHO001 (Rational self-interest) [independent -- no intra-domain deps; axiom]
```

**Acyclicity verification**: All arrows point from earlier items to later items. PRIM-CHO001 is the root; AX-CHO001 is independent (it is an axiom, not defined from other items). No item depends on an item listed after it. The graph is a DAG.

## 9. Cross-Domain Interface

### Exports

| ID | Concept | Imported by |
|----|---------|-------------|
| PRIM-CHO001 | Scarcity reasoning | MKT, MAC, POL |
| PRIM-CHO002 | Opportunity cost reasoning | MKT, MAC, POL |
| PRIM-CHO003 | Marginal analysis | MKT, MAC, POL |
| PRIM-CHO004 | Incentive reasoning | MKT, POL |
| PRIM-CHO005 | Trade and specialization reasoning | MKT, MAC |
| DEF-CHO001 | Production possibilities frontier | MAC |
| DEF-CHO002 | Diminishing marginal returns | MKT |
| DEF-CHO003 | Comparative advantage | MKT, MAC |
| AX-CHO001 | Rational self-interest | MKT, MAC, MON, POL |

### Imports

None. CHO is the root domain and imports nothing from any other domain.

## 10. Difficulty Tiers

| ID | Concept | Tier | Justification |
|----|---------|------|---------------|
| PRIM-CHO001 | Scarcity reasoning | C | Foundational: every subsequent concept requires recognizing that resources are limited and choices must be made |
| PRIM-CHO002 | Opportunity cost reasoning | C | Core threshold concept: transforms cost from a price-tag question into a tradeoff question; prerequisite for comparative advantage and all policy analysis |
| PRIM-CHO003 | Marginal analysis | C | Core reasoning framework: the operational logic behind every optimization decision; required for MKT (profit maximization, consumer choice) |
| PRIM-CHO004 | Incentive reasoning | C | Core predictive tool: the bridge from individual decisions to systemic outcomes; essential for policy analysis (POL) |
| PRIM-CHO005 | Trade and specialization reasoning | C | Core counterintuitive insight: challenges the zero-sum intuition; required for understanding international trade (MAC) |
| DEF-CHO001 | Production possibilities frontier | C | Core visualization: makes scarcity, tradeoffs, and opportunity cost concrete in a single diagram; used in MAC for growth analysis |
| DEF-CHO002 | Diminishing marginal returns | C | Core production concept: explains why marginal cost rises; required for supply reasoning (MKT) |
| DEF-CHO003 | Comparative advantage | C | Core trade concept: the formal criterion for mutually beneficial specialization; required for trade analysis (MKT, MAC) |
| AX-CHO001 | Rational self-interest | C | Core behavioral axiom: without it, incentive reasoning and supply/demand have no behavioral foundation |

**Tier constraint verification**: All 9 items are Core. No Enrichment items exist in CHO. The domain is the root of the entire taxonomy and all items are required by downstream Core items.

## 11. Self-Audit Checklist

- [x] Every PRIM has: reasoning move formulation ("Given X, do Y to determine Z"), description, semi-formal statement, depends, ownership, source, referenced-by, tier, real-world hook
- [x] Every DEF depends only on previously listed PRIM/DEF (check intra-domain dependency graph: DEF-CHO001 depends on PRIM-CHO001, PRIM-CHO002; DEF-CHO002 depends on PRIM-CHO003; DEF-CHO003 depends on PRIM-CHO002, PRIM-CHO005)
- [x] Every cross-domain reference uses full `{Type}-{Code}{Number}` format
- [x] Every import is listed in the source domain's exports (N/A -- CHO has no imports; CHO's exports are listed and match the Primitive Registry in CONVENTIONS.md Section 9)
- [x] Dissolution argument is present and non-trivial (at least 2 sentences explaining why CHO is distinct from MKT, MAC, MON, and POL)
- [x] Real-world hooks cover everyday non-major contexts (grocery budgets, college decisions, studying, plastic bags, career choices, coffee shops, Valentine's roses)
- [x] Intra-domain dependency graph is acyclic (verified: PRIM-CHO001 is root; all edges point from earlier to later items; AX-CHO001 is independent)
- [x] Tier annotations (C/E) are present on all 9 items
- [x] No PRIM/DEF duplicates an entry in another domain (checked against Primitive Registry in CONVENTIONS.md Section 9)
- [x] Reasoning moves are genuinely "Given X, do Y" cognitive operations (not mere topic labels or vocabulary words)
