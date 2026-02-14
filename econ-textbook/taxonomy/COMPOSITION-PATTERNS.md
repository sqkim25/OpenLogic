# COMPOSITION-PATTERNS v0.1

Cross-domain composition patterns for the economics taxonomy. Each pattern documents a reasoning chain that **genuinely requires** primitives from two or more domains -- removing any domain breaks the reasoning. Full specifications follow the template in CONVENTIONS.md Section 11.

**Total**: 7 patterns (7 Core)

**Governing constraint**: Every pattern listed here MUST be irreducibly cross-domain. If the reasoning chain can be completed using a single domain's primitives, it is not a composition pattern but an intra-domain result and MUST be moved to the relevant domain spec.

---

## CP-001: **How Prices Allocate Scarce Resources**

- **Domains**: CHO x MKT
- **Statement**: Given a society facing scarcity, show how the price mechanism (supply and demand) translates individual opportunity cost calculations into an economy-wide resource allocation without central planning.
- **Natural language**: Scarcity forces choices; prices coordinate those choices. Each individual computes their opportunity cost and responds to price incentives. When millions of individuals do this simultaneously, the market price emerges as the coordination signal that allocates resources to their highest-valued uses. CHO provides the decision logic (each agent optimizes at the margin); MKT provides the coordination mechanism (the price system aggregates those decisions into an efficient outcome). Neither domain alone explains resource allocation: CHO explains why individuals behave as they do, but not how their behaviors cohere into a market outcome; MKT explains market equilibrium, but the equilibrium depends on individual decision logic from CHO.
- **Key dependencies**:

| Domain | IDs |
|--------|-----|
| CHO | PRIM-CHO001 (scarcity reasoning), PRIM-CHO002 (opportunity cost reasoning), PRIM-CHO003 (marginal analysis), PRIM-CHO004 (incentive reasoning) |
| MKT | PRIM-MKT001 (demand reasoning), PRIM-MKT002 (supply reasoning), PRIM-MKT003 (equilibrium reasoning) |

- **Real-world hook**: "How does a grocery store in Minneapolis know how much bread to stock?"
- **Reasoning chain**:
  1. **PRIM-CHO001** (scarcity): Wheat, labor, oven capacity, and shelf space are all scarce. The bakery, the grocery store, and the consumer all face constraints.
  2. **PRIM-CHO002** + **PRIM-CHO003** (opportunity cost + marginal analysis): The bakery compares the marginal cost of producing one more loaf to the price it can sell it for. Consumers compare the marginal benefit of one more loaf to its price and their budget.
  3. **PRIM-CHO004** (incentive reasoning): If bread prices rise (perhaps due to a wheat shortage), consumers buy less and bakers produce more -- both responding to the price incentive.
  4. **PRIM-MKT001** + **PRIM-MKT002** (demand + supply): These individual decisions aggregate into demand and supply curves for bread.
  5. **PRIM-MKT003** (equilibrium): The market price adjusts until quantity demanded equals quantity supplied. No central planner decided how much bread Minneapolis needs. The price did it.
- **Tier**: C
- **Significance**: This is the foundational cross-domain pattern -- it is essentially Adam Smith's "invisible hand." Without CHO, we cannot explain why agents behave as they do. Without MKT, we cannot explain how their behaviors cohere into an efficient allocation. This pattern explains why market economies generally outperform centrally planned economies at resource allocation: prices aggregate dispersed information that no single planner can possess.

---

## CP-002: **Why Trade Makes Both Sides Better Off**

- **Domains**: CHO x MKT x MAC
- **Statement**: Given two countries with different opportunity costs of production, show how specialization according to comparative advantage and voluntary trade through markets increases total output and makes both countries better off, even if one country is better at producing everything.
- **Natural language**: Comparative advantage (CHO) determines who should produce what. Markets (MKT) facilitate the voluntary exchange through which both countries access a consumption bundle outside their individual PPF. The aggregate effect (MAC) is higher GDP for both countries. This pattern integrates the individual decision logic (CHO: each country optimizes its production), the exchange mechanism (MKT: trade occurs at a mutually beneficial price), and the aggregate outcome (MAC: both countries' total output and consumption increase).
- **Key dependencies**:

| Domain | IDs |
|--------|-----|
| CHO | PRIM-CHO002 (opportunity cost reasoning), PRIM-CHO005 (trade and specialization reasoning), DEF-CHO003 (comparative advantage), DEF-CHO001 (PPF) |
| MKT | PRIM-MKT003 (equilibrium reasoning), DEF-MKT004 (consumer and producer surplus) |
| MAC | PRIM-MAC001 (GDP reasoning), DEF-MAC005 (trade balance) |

- **Real-world hook**: "Why do Americans buy roses from Colombia and Colombians buy software from America?"
- **Reasoning chain**:
  1. **PRIM-CHO002** (opportunity cost): Colombia's opportunity cost of growing roses is low (warm climate, cheap labor for agriculture). America's opportunity cost of producing software is low (tech workforce, capital, research universities).
  2. **DEF-CHO003** (comparative advantage): Colombia has comparative advantage in roses; America has comparative advantage in software.
  3. **PRIM-CHO005** (trade and specialization): Both countries specialize in their comparative advantage good.
  4. **DEF-CHO001** (PPF): Without trade, each country is limited to its own PPF. With trade, each country can consume outside its PPF -- more roses AND more software than either could produce alone.
  5. **PRIM-MKT003** (equilibrium): The international price of roses settles between Colombia's and America's opportunity costs, ensuring both countries gain from trade.
  6. **PRIM-MAC001** (GDP reasoning): Both countries' GDP increases because specialization raises total output. The gains show up as higher total production.
- **Tier**: C
- **Significance**: This pattern explains why international trade is not zero-sum. It is the most counterintuitive result for non-majors, who often believe that imports "steal" domestic jobs and that trade deficits mean "losing." The pattern requires CHO (the decision logic of specialization), MKT (the price mechanism for exchange), and MAC (the aggregate outcome). Removing any domain breaks the explanation.

---

## CP-003: **Tax Incidence and Deadweight Loss**

- **Domains**: MKT x POL
- **Statement**: Given a tax imposed in a market, determine who bears the economic burden (incidence) and how much surplus is destroyed (deadweight loss) by combining market equilibrium analysis with policy reasoning.
- **Natural language**: The market provides the equilibrium and elasticity framework; policy provides the tax and the welfare evaluation. Tax incidence is deeply counterintuitive: who pays the tax legally does not determine who bears the burden economically. The burden falls on the less elastic side. This pattern requires MKT (to analyze how the market adjusts to the tax wedge) and POL (to evaluate the welfare consequences and design better tax policy).
- **Key dependencies**:

| Domain | IDs |
|--------|-----|
| MKT | PRIM-MKT003 (equilibrium reasoning), PRIM-MKT004 (elasticity reasoning), DEF-MKT004 (consumer and producer surplus), DEF-MKT005 (deadweight loss) |
| POL | DEF-POL002 (tax incidence), AX-POL002 (no free lunch -- the tax has costs) |

- **Real-world hook**: "Who really pays the tax on cigarettes -- the smoker or the tobacco company?"
- **Reasoning chain**:
  1. **PRIM-MKT003** (equilibrium): Before the tax, the market is in equilibrium at P* and Q*. The tax creates a wedge between the price buyers pay and the price sellers receive.
  2. **PRIM-MKT004** (elasticity): Cigarette demand is highly inelastic (addicted smokers cannot easily quit). Supply is relatively elastic (tobacco companies can adjust production). The inelastic side (consumers) bears most of the tax burden.
  3. **DEF-MKT004** (surplus): Consumer surplus falls significantly; producer surplus falls less. Government collects tax revenue.
  4. **DEF-MKT005** (deadweight loss): Some transactions that would have occurred at the competitive equilibrium do not occur under the tax. That lost surplus is deadweight loss -- a pure waste.
  5. **DEF-POL002** (tax incidence): The formal analysis shows that regardless of whether the tax is legally imposed on the buyer or seller, the economic burden distribution is the same -- determined entirely by relative elasticities.
  6. **AX-POL002** (no free lunch): The tax revenue is not free. It comes at the cost of DWL and the burden borne by consumers and producers.
- **Tier**: C
- **Significance**: Tax incidence is one of the most practically important results in economics for citizens. Non-majors will vote on tax proposals throughout their lives. This pattern teaches them that the legal assignment of a tax (e.g., "payroll tax on employers") does not determine the economic reality (workers bear much of the burden through lower wages). Without MKT, there is no framework for analyzing market adjustment. Without POL, there is no welfare evaluation.

---

## CP-004: **How the Fed Fights Recession**

- **Domains**: MON x MAC x POL
- **Statement**: Given a recessionary gap (actual GDP below potential), trace the complete monetary policy transmission mechanism from the Fed's decision to buy bonds, through the banking system, interest rates, investment, aggregate demand, and finally to GDP and employment.
- **Natural language**: The Fed uses its monetary tools (MON) to shift aggregate demand (MAC) as a deliberate policy intervention (POL). This is the canonical example of how the three domains work together: MON provides the financial plumbing (how money supply changes affect interest rates), MAC provides the aggregate framework (how interest rate changes affect GDP), and POL provides the policy reasoning (when and why to intervene, and what the tradeoffs are).
- **Key dependencies**:

| Domain | IDs |
|--------|-----|
| MON | DEF-MON003 (central bank operations), PRIM-MON003 (interest rate reasoning), PRIM-MON004 (money supply reasoning) |
| MAC | DEF-MAC002 (aggregate demand), PRIM-MAC005 (business cycle reasoning), PRIM-MAC002 (unemployment reasoning) |
| POL | PRIM-POL003 (monetary policy reasoning), AX-POL002 (no free lunch -- stimulus has costs) |

- **Real-world hook**: "What did the Fed actually do during the COVID-19 recession?"
- **Reasoning chain**:
  1. **PRIM-MAC005** (business cycle): The economy is in contraction. GDP is falling, unemployment is rising, businesses are cutting investment.
  2. **PRIM-POL003** (monetary policy reasoning): The Fed decides to stimulate the economy. The diagnosis: insufficient aggregate demand.
  3. **DEF-MON003** (central bank operations): The Fed buys government bonds (open-market purchase), injecting reserves into the banking system.
  4. **PRIM-MON004** (money supply): The monetary base increases. Through the money multiplier, the total money supply expands.
  5. **PRIM-MON003** (interest rate): With more money available for lending, the interest rate falls. Mortgage rates, business loan rates, and credit card rates all decline.
  6. **DEF-MAC002** (aggregate demand): Lower interest rates stimulate investment (firms borrow to expand) and consumption (consumers borrow for homes, cars). AD shifts right.
  7. **PRIM-MAC002** (unemployment): As GDP rises, firms hire more workers. Unemployment falls.
  8. **AX-POL002** (no free lunch): The stimulus is not costless. If the Fed keeps rates too low for too long, excess money growth leads to inflation. This is exactly what happened: aggressive 2020-2021 stimulus contributed to 2022 inflation.
- **Tier**: C
- **Significance**: This pattern is the most complex cross-domain chain in the taxonomy, linking three domains in a sequential causal mechanism. It is also the most practically relevant: the Fed's actions affect every American's mortgage rate, job prospects, and savings returns. Without MON, students cannot understand HOW the Fed's actions affect the economy. Without MAC, they cannot understand WHAT aggregate outcome the Fed is targeting. Without POL, they cannot evaluate WHETHER the Fed's action was appropriate or what tradeoffs it involved.

---

## CP-005: **The Minimum Wage Debate**

- **Domains**: CHO x MKT x POL
- **Statement**: Given a proposal to raise the minimum wage, analyze its effects on employment, worker welfare, and economic efficiency by combining individual decision logic, labor market equilibrium, and policy tradeoff analysis.
- **Natural language**: The minimum wage debate is the paradigmatic example of how economic reasoning does not give a simple answer. CHO provides the decision logic (workers and firms respond to incentives). MKT provides the market analysis (a price floor above equilibrium creates a surplus of labor -- unemployment). POL provides the tradeoff evaluation (some workers benefit from higher wages, but others may lose their jobs; the net effect depends on labor market elasticity and the size of the increase).
- **Key dependencies**:

| Domain | IDs |
|--------|-----|
| CHO | PRIM-CHO004 (incentive reasoning), PRIM-CHO003 (marginal analysis) |
| MKT | PRIM-MKT003 (equilibrium reasoning), PRIM-MKT004 (elasticity reasoning), DEF-MKT003 (price ceiling and floor) |
| POL | AX-POL001 (efficiency-equity tradeoff), AX-POL002 (no free lunch) |

- **Real-world hook**: "Should the minimum wage be raised to $15/hour?"
- **Reasoning chain**:
  1. **DEF-MKT003** (price floor): The minimum wage is a price floor in the labor market. If set above the equilibrium wage, it creates a surplus of labor (more workers want jobs at $15 than firms want to hire at $15).
  2. **PRIM-MKT004** (elasticity): The employment effect depends on labor demand elasticity. If demand is inelastic (firms cannot easily replace workers with machines), the job losses are small. If elastic, job losses are significant.
  3. **PRIM-CHO004** (incentive reasoning): At a higher wage, more workers enter the labor force (incentive to work increases). But firms substitute toward automation, reduce hours, or raise prices (incentive to minimize labor costs increases). Both responses are predictable from incentive reasoning.
  4. **PRIM-CHO003** (marginal analysis): Each firm decides whether to keep each worker based on whether the worker's marginal product exceeds the new, higher wage. Workers whose marginal product is below $15 are the ones most likely to lose their jobs -- typically the least-skilled workers the policy is trying to help.
  5. **AX-POL001** (efficiency-equity tradeoff): The minimum wage increases equity (those who keep their jobs earn more) but may reduce efficiency (some mutually beneficial employment relationships are destroyed). The tradeoff is real.
  6. **AX-POL002** (no free lunch): Higher wages for some workers come at the cost of unemployment for others, higher prices for consumers, and reduced profits for firms. The benefits are concentrated and visible; the costs are diffuse and often invisible.
- **Tier**: C
- **Significance**: The minimum wage debate is the single most-discussed economic policy issue for non-majors. It perfectly illustrates how economic reasoning provides analytical clarity without dictating a political conclusion. Reasonable people can look at the same analysis and reach different conclusions based on how they weigh the efficiency costs against the equity benefits. The pattern requires CHO (incentive and marginal reasoning), MKT (equilibrium and elasticity), and POL (tradeoff evaluation). Removing any domain reduces the analysis to a slogan.

---

## CP-006: **Inflation and the Cost of Living**

- **Domains**: MAC x MON
- **Statement**: Given data on money supply growth and aggregate output growth, predict the direction and approximate magnitude of inflation, and trace the redistribution effects across different economic groups.
- **Natural language**: Inflation is where macro measurement (MAC) meets monetary mechanics (MON). MAC defines and measures inflation through the CPI and distinguishes real from nominal values. MON explains one of the primary causes: when the money supply grows faster than real output, the excess money pushes up prices. The quantity theory of money (MV = PY) is the formal connection. Neither domain alone fully explains inflation: MAC can measure it but needs MON to explain the monetary cause; MON can explain the money-price connection but needs MAC to measure the aggregate outcome and assess the redistribution effects.
- **Key dependencies**:

| Domain | IDs |
|--------|-----|
| MAC | PRIM-MAC003 (inflation reasoning), PRIM-MAC004 (price level reasoning), DEF-MAC001 (nominal vs. real values) |
| MON | PRIM-MON004 (money supply reasoning), PRIM-MON001 (money functions reasoning) |

- **Real-world hook**: "Why did inflation spike to 9% in 2022 after years near 2%?"
- **Reasoning chain**:
  1. **PRIM-MON004** (money supply reasoning): Between 2020 and 2022, the Fed expanded the monetary base dramatically (quantitative easing + near-zero rates). The money supply (M2) grew by over 40% in two years.
  2. **PRIM-MON001** (money functions): As more money chased the same (or fewer, due to supply chain disruptions) goods, money's store-of-value function degraded -- each dollar bought less.
  3. **PRIM-MAC004** (price level): The general price level rose economy-wide, not just in specific markets. This was a macro phenomenon, not a micro one.
  4. **PRIM-MAC003** (inflation reasoning): The CPI measured the rate of increase at 9.1% year-over-year in June 2022. Demand-pull inflation (stimulus-fueled spending) combined with cost-push inflation (supply chain disruptions).
  5. **DEF-MAC001** (nominal vs. real): Wages rose 5% nominally but fell 4% in real terms. Borrowers with fixed-rate mortgages benefited; savers and retirees on fixed incomes were hurt. Inflation redistributed wealth from creditors to debtors.
- **Tier**: C
- **Significance**: Inflation is the macroeconomic phenomenon that most directly affects non-majors' daily lives. This pattern connects the abstract monetary mechanism (money supply growth) to the concrete experience (higher grocery bills). Without MAC, students can see prices rising but cannot measure, categorize, or assess the redistribution effects. Without MON, students can see prices rising but cannot understand the monetary causes or evaluate the Fed's response.

---

## CP-007: **Correcting Pollution Externalities**

- **Domains**: MKT x POL
- **Statement**: Given a negative externality (pollution), design a policy correction (Pigouvian tax, cap-and-trade, or regulation) that aligns private costs with social costs, and evaluate the efficiency and practical tradeoffs of each approach.
- **Natural language**: The market produces pollution because the market price does not reflect the full social cost. MKT diagnoses the failure; POL prescribes the cure. This pattern compares three correction approaches: (1) Pigouvian tax (set tax = external cost, simple but requires knowing the cost), (2) cap-and-trade (set quantity limit, let the market determine the price, finds the efficient allocation), (3) command-and-control regulation (mandate technology or emission limits, less efficient but easier to enforce). Each approach uses market reasoning (MKT) to understand the problem and policy reasoning (POL) to design and evaluate the solution.
- **Key dependencies**:

| Domain | IDs |
|--------|-----|
| MKT | DEF-MKT006 (externality), DEF-MKT005 (deadweight loss), PRIM-MKT003 (equilibrium reasoning) |
| POL | PRIM-POL001 (market failure correction reasoning), PRIM-CHO004 (incentive reasoning, imported by POL), AX-POL002 (no free lunch) |

- **Real-world hook**: "What is the best way to reduce carbon emissions?"
- **Reasoning chain**:
  1. **DEF-MKT006** (externality): Carbon emissions are a negative externality. The social cost of burning fossil fuels (climate damage) exceeds the private cost (fuel price). The market overproduces emissions.
  2. **DEF-MKT005** (deadweight loss): The overproduction creates DWL -- the excess emissions cost society more than the value of the additional output they enable.
  3. **PRIM-POL001** (market failure correction): Three approaches:
     - **Pigouvian tax**: Set a carbon tax equal to the marginal external cost. Firms face the true social cost and reduce emissions to the efficient level. Advantage: simple, raises revenue. Disadvantage: requires estimating the external cost accurately.
     - **Cap-and-trade**: Set a total emissions cap, issue tradeable permits. Firms that can reduce emissions cheaply do so and sell permits to firms that cannot. Advantage: achieves the target quantity regardless of cost estimation. Disadvantage: volatile permit prices.
     - **Command-and-control**: Mandate specific emission limits or technologies. Advantage: certainty of compliance. Disadvantage: does not minimize total abatement cost (no flexibility for firms to find cheapest reductions).
  4. **PRIM-CHO004** (incentive reasoning, used by POL): All three approaches work by changing incentives. The tax makes polluting more expensive. Cap-and-trade makes polluting costly (must buy permits). Regulation makes polluting illegal beyond a threshold.
  5. **AX-POL002** (no free lunch): All three approaches have costs -- higher energy prices for consumers, compliance costs for firms, administrative costs for government. The question is which approach achieves the target reduction at the lowest total cost.
- **Tier**: C
- **Significance**: Climate change is the defining policy challenge for today's non-majors. This pattern equips them to evaluate competing policy proposals using economic reasoning rather than political slogans. Without MKT, students cannot understand WHY the market overproduces pollution. Without POL, students cannot evaluate the correction options or their tradeoffs. The pattern also illustrates a general principle: economists prefer market-based solutions (tax, cap-and-trade) over command-and-control because they harness incentive reasoning and allow flexibility, but all approaches involve tradeoffs.

---

## Summary Table

| ID | Name | Domains | Tier | Real-World Hook |
|----|------|---------|------|-----------------|
| CP-001 | How Prices Allocate Scarce Resources | CHO x MKT | C | How does a grocery store know how much bread to stock? |
| CP-002 | Why Trade Makes Both Sides Better Off | CHO x MKT x MAC | C | Why do Americans buy Colombian roses? |
| CP-003 | Tax Incidence and Deadweight Loss | MKT x POL | C | Who really pays the cigarette tax? |
| CP-004 | How the Fed Fights Recession | MON x MAC x POL | C | What did the Fed do during COVID-19? |
| CP-005 | The Minimum Wage Debate | CHO x MKT x POL | C | Should the minimum wage be $15/hour? |
| CP-006 | Inflation and the Cost of Living | MAC x MON | C | Why did inflation spike to 9% in 2022? |
| CP-007 | Correcting Pollution Externalities | MKT x POL | C | What is the best way to reduce carbon emissions? |

### Domain Coverage Matrix

Every domain appears in at least two composition patterns, confirming that no domain is isolated from cross-domain reasoning:

| Domain | Patterns |
|--------|----------|
| CHO | CP-001, CP-002, CP-005 |
| MKT | CP-001, CP-002, CP-003, CP-005, CP-007 |
| MAC | CP-002, CP-004, CP-006 |
| MON | CP-004, CP-006 |
| POL | CP-003, CP-004, CP-005, CP-007 |

### Irreducibility Check

Each pattern has been verified to be irreducibly cross-domain. For each pattern, removing any participating domain breaks the reasoning chain:

- **CP-001**: Without CHO, no explanation for why agents behave as they do. Without MKT, no coordination mechanism.
- **CP-002**: Without CHO, no comparative advantage logic. Without MKT, no trade mechanism. Without MAC, no aggregate outcome measurement.
- **CP-003**: Without MKT, no equilibrium/elasticity framework. Without POL, no welfare evaluation.
- **CP-004**: Without MON, no financial transmission mechanism. Without MAC, no aggregate target. Without POL, no policy reasoning.
- **CP-005**: Without CHO, no incentive/marginal analysis. Without MKT, no labor market equilibrium. Without POL, no tradeoff evaluation.
- **CP-006**: Without MAC, no inflation measurement or redistribution analysis. Without MON, no monetary cause explanation.
- **CP-007**: Without MKT, no externality diagnosis. Without POL, no correction design.
