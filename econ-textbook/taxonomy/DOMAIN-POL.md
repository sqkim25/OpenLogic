# DOMAIN-POL v0.1

## 0. Sources & Assumptions

- SRC-POL001: Stiglitz, *Economics of the Public Sector*, 4th ed., 2015, Ch. 1--6 (market failure, public goods, externalities, tax policy)
- SRC-POL002: Musgrave, *The Theory of Public Finance*, 1959 (foundational treatment of allocation, distribution, and stabilization functions of government)
- SRC-POL003: Okun, *Equality and Efficiency: The Big Tradeoff*, 1975 (efficiency-equity tension)
- SRC-GLB001: OpenStax, *Principles of Economics*, 3rd ed., 2023, Ch. 12--15, 30--32
- SRC-GLB002: Mankiw, *Principles of Economics*, 9th ed., 2021, Ch. 8--12, 34--36
- SRC-GLB007: Samuelson & Nordhaus, *Economics*, 19th ed., 2010, Ch. 16--19
- ASM-POL001: Policy analysis is presented as tradeoff analysis using the taxonomy's reasoning moves, NOT as political advocacy. The same primitives can support different policy conclusions depending on empirical assumptions and value judgments. Justification: political neutrality is essential for non-majors from all political backgrounds (ASM-GLB005).
- ASM-POL002: Government is treated as a rational actor facing constraints, not as an omniscient planner. Government failure (inefficiency, unintended consequences, rent-seeking) is presented alongside market failure. Justification: balanced treatment of both market and government imperfections produces better economic reasoning.

## 1. Domain Intent

- **Governing question**: How do governments influence economic outcomes?
- **Scope**: The rationale for government intervention (market failures), the tools of fiscal policy (government spending, taxation, borrowing), the deployment of monetary policy (using central bank tools to manage the economy), regulation, trade policy, and the fundamental tradeoffs inherent in all policy decisions (efficiency vs. equity, intended vs. unintended consequences). POL provides the intervention layer: how governments attempt to correct market failures, stabilize the business cycle, redistribute income, and promote growth.
- **Non-goals**: How individual agents make decisions (CHO). How markets work in the absence of intervention (MKT). How aggregate outcomes are measured (MAC). How the financial system mechanically operates (MON). POL uses all four upstream domains as inputs but asks a distinct question: what should the government DO, and what are the tradeoffs?
- **Dissolution argument**: Policy analysis cannot be reduced to any upstream domain. MKT identifies that externalities exist; POL decides whether and how to correct them (Pigouvian tax, cap-and-trade, regulation). MAC measures that unemployment is high; POL decides whether to respond with fiscal stimulus and evaluates the tradeoffs. MON describes how the Fed's tools work; POL analyzes when and why to deploy them. Removing POL would leave the taxonomy able to describe economic mechanisms but unable to evaluate government actions -- and evaluating government actions is perhaps the most practically important skill for non-major citizens. Policy analysis requires combining reasoning moves from CHO (tradeoffs, incentives), MKT (efficiency, market failure), MAC (aggregate outcomes), and MON (monetary tools) with normative considerations (equity, fairness) that no upstream domain addresses. This normative dimension is unique to POL.
- **Threshold schema mapping**: Intention --> Outcome. The foundational conceptual shift in POL is recognizing that policy intentions and policy outcomes frequently diverge because of incentive effects, unintended consequences, and implementation challenges. Rent control is intended to help renters but often reduces housing supply. Tariffs are intended to protect domestic jobs but often raise prices for consumers and provoke retaliation. Students who fail to cross this threshold evaluate policies by their stated goals rather than their actual effects.

## 2. Prerequisites

POL depends on all four upstream domains:

| DEP ID | Imported Item | Reason |
|--------|---------------|--------|
| DEP-POL001 | PRIM-CHO001 (Scarcity reasoning) | Policy must allocate scarce government resources |
| DEP-POL002 | PRIM-CHO002 (Opportunity cost reasoning) | Every dollar spent on one program is a dollar not spent on another |
| DEP-POL003 | PRIM-CHO003 (Marginal analysis) | Optimal policy balances marginal benefit of intervention vs. marginal cost |
| DEP-POL004 | PRIM-CHO004 (Incentive reasoning) | Policies work by changing incentives; predicting responses is essential |
| DEP-POL005 | AX-CHO001 (Rational self-interest) | Policy analysis assumes agents respond to policy-created incentives |
| DEP-POL006 | PRIM-MKT003 (Equilibrium reasoning) | Policy effects are analyzed using supply-demand equilibrium shifts |
| DEP-POL007 | PRIM-MKT004 (Elasticity reasoning) | Tax incidence depends on relative elasticities |
| DEP-POL008 | PRIM-MKT005 (Market structure reasoning) | Antitrust and regulation target market power |
| DEP-POL009 | DEF-MKT003 (Price ceiling and floor) | Price controls are a policy instrument |
| DEP-POL010 | DEF-MKT004 (Consumer and producer surplus) | Welfare analysis of policy uses surplus measures |
| DEP-POL011 | DEF-MKT005 (Deadweight loss) | Policy-induced DWL measures efficiency cost |
| DEP-POL012 | DEF-MKT006 (Externality) | Externalities are the primary microeconomic rationale for intervention |
| DEP-POL013 | DEF-MKT007 (Public good) | Public goods justify government provision |
| DEP-POL014 | PRIM-MAC001 (GDP reasoning) | Fiscal and monetary policy target GDP growth |
| DEP-POL015 | PRIM-MAC002 (Unemployment reasoning) | Stabilization policy targets unemployment |
| DEP-POL016 | PRIM-MAC003 (Inflation reasoning) | Monetary policy targets inflation |
| DEP-POL017 | PRIM-MAC005 (Business cycle reasoning) | Stabilization policy responds to the business cycle |
| DEP-POL018 | DEF-MAC002 (Aggregate demand) | Fiscal/monetary policy operates through AD shifts |
| DEP-POL019 | DEF-MAC003 (Aggregate supply) | Supply-side policy operates through AS shifts |
| DEP-POL020 | PRIM-MON003 (Interest rate reasoning) | Monetary policy operates through interest rate changes |
| DEP-POL021 | PRIM-MON004 (Money supply reasoning) | Monetary policy changes the money supply |
| DEP-POL022 | DEF-MON003 (Central bank operations) | Monetary policy uses Fed tools |

## 3. Primitives

- PRIM-POL001: **Market failure correction reasoning**
  - Reasoning move: Given evidence of a market failure (externality, public good, market power, information asymmetry), design a correction mechanism (tax, subsidy, regulation, property rights assignment, government provision) and evaluate its efficiency and equity consequences.
  - Description: The cognitive operation of moving from diagnosis (the market is producing an inefficient outcome) to prescription (a government intervention that moves the outcome closer to efficiency). Market failure correction reasoning requires: (1) identifying the specific failure (which of MKT's failure types?); (2) selecting an appropriate tool (Pigouvian tax for negative externalities, subsidy for positive externalities, government provision for public goods, antitrust for monopoly); (3) evaluating the tradeoffs (the correction has costs -- administrative costs, distorted incentives, possible government failure). This primitive applies CHO's incentive reasoning to policy design: the intervention works by changing the incentives facing agents so that their self-interested behavior produces a more efficient outcome.
  - Semi-formal: Given market failure F producing outcome Q_market != Q_efficient: (1) identify F type (externality, public good, monopoly, information asymmetry); (2) select tool T that aligns private incentives with social optimum; (3) evaluate: does T reduce DWL? Does T create new distortions? Net benefit of T = DWL_reduced - implementation_cost - new_distortions. T is justified iff net benefit > 0.
  - Depends: DEF-MKT006 (externality -- the primary market failure POL corrects), DEF-MKT005 (deadweight loss -- the efficiency cost POL tries to reduce), PRIM-CHO004 (incentive reasoning -- policy corrections work by changing incentives)
  - Ownership: POL
  - Source: SRC-GLB001 (OpenStax Ch. 12--13), SRC-GLB002 (Mankiw Ch. 10--11), SRC-POL001 (Stiglitz Ch. 4--5)
  - Referenced by: ---
  - Tier: C
  - Real-world hook: Cars emit CO2 (negative externality). The market price of gasoline does not include the climate damage cost. A carbon tax adds that cost to the price, so drivers face the true social cost when deciding how much to drive. The tax does not ban driving -- it changes the incentive so that the market produces closer to the efficient amount of driving. This is market failure correction in action.

- PRIM-POL002: **Fiscal policy reasoning**
  - Reasoning move: Given a macroeconomic problem (recession, overheating economy, high unemployment), determine the appropriate fiscal policy response (increase/decrease government spending, cut/raise taxes) and trace its effect through aggregate demand, multiplier, and budget consequences.
  - Description: The cognitive operation of using government spending and taxation to manage the macroeconomy. Fiscal policy reasoning combines macro analysis (where are we in the business cycle?) with policy design (what spending or tax change will shift AD in the right direction?) and tradeoff evaluation (what are the budget consequences?). In a recession, expansionary fiscal policy (increase G or cut T) shifts AD right, increasing GDP and reducing unemployment -- but increases the budget deficit. In an overheating economy, contractionary fiscal policy (cut G or raise T) shifts AD left, reducing inflation -- but may cause a recession. The key insight is that fiscal policy involves inescapable tradeoffs: stimulating the economy today requires borrowing that must be repaid tomorrow.
  - Semi-formal: Recession: output < potential, unemployment > natural rate. Expansionary fiscal policy: increase G or decrease T --> AD shifts right --> GDP increases, unemployment falls. Budget effect: deficit increases (G > T). Overheating: output > potential, inflation accelerating. Contractionary fiscal policy: decrease G or increase T --> AD shifts left --> inflation falls. Budget effect: deficit decreases. Tradeoff: short-run stabilization vs. long-run fiscal sustainability.
  - Depends: DEF-MAC002 (aggregate demand -- fiscal policy shifts AD), PRIM-MAC005 (business cycle reasoning -- fiscal policy responds to the cycle), PRIM-CHO002 (opportunity cost reasoning -- government spending has opportunity costs)
  - Ownership: POL
  - Source: SRC-GLB001 (OpenStax Ch. 30), SRC-GLB002 (Mankiw Ch. 34), SRC-MAC002 (Keynes 1936)
  - Referenced by: ---
  - Tier: C
  - Real-world hook: During the COVID-19 recession, the US government passed over $5 trillion in stimulus (PPP loans, stimulus checks, enhanced unemployment). This was expansionary fiscal policy on a massive scale: shift AD right to prevent economic collapse. It worked -- unemployment fell from 14.7% to 3.5% within two years. But the cost was a surge in the national debt and, combined with supply disruptions, contributed to 9% inflation. Every fiscal policy decision involves this kind of tradeoff.

- PRIM-POL003: **Monetary policy reasoning**
  - Reasoning move: Given a macroeconomic problem (recession or inflation), determine the appropriate monetary policy response (expand or contract the money supply via central bank tools) and trace its effect through interest rates, borrowing, investment, aggregate demand, and prices.
  - Description: The cognitive operation of using central bank tools to manage the macroeconomy through the interest rate channel. Monetary policy reasoning combines: (1) diagnosis (what is the macroeconomic problem?); (2) prescription (should the central bank expand or contract the money supply?); (3) transmission mechanism (money supply change --> interest rate change --> investment/consumption change --> AD shift --> GDP/price level change); (4) tradeoff evaluation (expanding to fight recession risks future inflation; contracting to fight inflation risks recession). The key distinction from fiscal policy: monetary policy is faster (the Fed can act immediately; Congress takes months) but less targeted (interest rates affect the whole economy, not specific sectors).
  - Semi-formal: Recession: Fed expands money supply (buy bonds, lower rates) --> r falls --> I increases, C increases --> AD shifts right --> GDP increases, unemployment falls. Risk: if overdone, inflation rises. Inflation: Fed contracts money supply (sell bonds, raise rates) --> r rises --> I decreases, C decreases --> AD shifts left --> inflation falls. Risk: if overdone, recession occurs. Phillips curve tradeoff: in the short run, lower unemployment correlates with higher inflation, and vice versa.
  - Depends: DEF-MON003 (central bank operations -- the tools monetary policy uses), PRIM-MON003 (interest rate reasoning -- the channel through which monetary policy works), DEF-MAC002 (aggregate demand -- monetary policy operates by shifting AD), PRIM-MAC003 (inflation reasoning -- inflation is the primary target of monetary policy)
  - Ownership: POL
  - Source: SRC-GLB001 (OpenStax Ch. 28, 31), SRC-GLB002 (Mankiw Ch. 34), SRC-MON003 (Bernanke 2013)
  - Referenced by: ---
  - Tier: C
  - Real-world hook: In 2022-2023, the Fed raised interest rates from near-zero to over 5% -- the fastest increase in 40 years -- to fight 9% inflation. Mortgage rates doubled. Car loan rates surged. Business borrowing slowed. The goal: cool down AD to reduce inflation. The tradeoff: higher rates risked causing a recession. Monetary policy reasoning is the framework for evaluating whether the Fed made the right call.

## 4. Definitions

- DEF-POL001: **Government budget and deficit**
  - Reasoning move: Given data on government revenue (taxes) and spending (transfers, purchases, interest on debt), calculate the budget balance, identify whether the government is running a surplus or deficit, and connect the deficit to national debt and long-run fiscal sustainability.
  - Description: The government budget balance is revenue minus spending. A deficit (spending > revenue) must be financed by borrowing, adding to the national debt. A surplus (revenue > spending) allows debt repayment. The national debt is the accumulation of all past deficits minus all past surpluses. Budget reasoning corrects the common confusion between deficit (annual flow) and debt (cumulative stock). The key tradeoff: running deficits during recessions (countercyclical fiscal policy) is economically sensible but adds to long-run debt, which eventually requires higher taxes or reduced spending. Government budget reasoning is the fiscal counterpart of scarcity reasoning: governments, like individuals, face a budget constraint.
  - Semi-formal: Budget balance = tax revenue (T) - government spending (G + transfers + interest). Deficit = G - T > 0. Surplus = T - G > 0. National debt D_t = D_{t-1} + deficit_t. Debt-to-GDP ratio = D / GDP. Sustainability criterion: debt-to-GDP ratio must not grow without bound. Primary deficit = deficit - interest payments. If primary balance = 0 and interest rate < GDP growth rate, debt-to-GDP stabilizes.
  - Depends: PRIM-POL002 (fiscal policy reasoning -- the budget balance is the accounting consequence of fiscal policy), PRIM-CHO001 (scarcity reasoning -- government resources are finite)
  - Ownership: POL
  - Source: SRC-GLB001 (OpenStax Ch. 30), SRC-GLB002 (Mankiw Ch. 36)
  - Referenced by: ---
  - Tier: C
  - Real-world hook: The US national debt exceeded $34 trillion in 2024. Is that a crisis? Budget reasoning says: compare debt to GDP (currently about 120%), look at the interest cost (about 3% of GDP), and ask whether the economy is growing fast enough to sustain the debt. A $34 trillion debt in a $28 trillion economy is more sustainable than a $34 trillion debt in a $10 trillion economy. The raw number is less informative than the ratio.

- DEF-POL002: **Tax incidence**
  - Reasoning move: Given a tax levied on buyers or sellers in a market, determine who actually bears the economic burden of the tax (regardless of who legally pays it) by analyzing the relative elasticities of supply and demand.
  - Description: Tax incidence is the analysis of who bears the real burden of a tax. The key insight is deeply counterintuitive: it does not matter whether the tax is legally imposed on buyers or sellers -- the economic burden is shared based on relative elasticities. The more inelastic side bears more of the tax burden because they are less able to change their behavior to avoid the tax. If demand is inelastic and supply is elastic, consumers bear most of the burden (even if the tax is legally on producers). If supply is inelastic and demand is elastic, producers bear most of the burden. Tax incidence applies CHO's incentive reasoning (how do agents respond to the tax?) and MKT's elasticity reasoning (how responsive are buyers and sellers?) to a policy question.
  - Semi-formal: Tax t per unit. New equilibrium: P_buyers = P* + t_b, P_sellers = P* - t_s, where t_b + t_s = t. Share borne by buyers: t_b / t = E_s / (E_s + E_d), where E_s = supply elasticity, E_d = demand elasticity (absolute value). The more inelastic side bears the larger share. Deadweight loss of the tax = triangle between S and D from Q_tax to Q*; DWL = (1/2) * t * (Q* - Q_tax).
  - Depends: PRIM-MKT004 (elasticity reasoning -- tax burden depends on relative elasticities), PRIM-MKT003 (equilibrium reasoning -- tax creates a wedge in the market equilibrium), DEF-MKT005 (deadweight loss -- taxes create DWL)
  - Ownership: POL
  - Source: SRC-GLB001 (OpenStax Ch. 12), SRC-GLB002 (Mankiw Ch. 8), SRC-POL001 (Stiglitz Ch. 17)
  - Referenced by: ---
  - Tier: C
  - Real-world hook: When the government imposes a "payroll tax on employers," employers respond by offering lower wages. The tax is legally on employers but economically shared with workers. Similarly, a "luxury tax on yacht buyers" in 1990 was expected to burden the wealthy, but it actually devastated boat builders (supply was elastic; rich people just bought other luxury goods). The yacht tax was repealed because it fell on the wrong people. Tax incidence reasoning prevents this mistake.

- DEF-POL003: **Trade policy**
  - Reasoning move: Given a proposed trade restriction (tariff, quota, trade agreement), determine its effects on domestic consumers, producers, government revenue, and overall efficiency using supply-demand analysis and comparative advantage reasoning.
  - Description: Trade policy encompasses government actions that restrict or promote international trade. A tariff (tax on imports) raises the domestic price, benefiting domestic producers (they can charge more) and generating government revenue, but hurting domestic consumers (they pay higher prices) and creating deadweight loss (efficient foreign production is replaced by less efficient domestic production). A quota (quantity limit on imports) has similar effects but without government revenue (the revenue goes to foreign producers or whoever holds the import licenses). Free trade maximizes total surplus because it allows countries to specialize according to comparative advantage. Trade restrictions reduce total surplus but may be adopted for non-efficiency reasons (protecting domestic jobs, national security, infant industries). Trade policy reasoning applies CHO's comparative advantage to the policy domain.
  - Semi-formal: Tariff t on imported good: domestic price rises from P_world to P_world + t. Consumer surplus falls. Producer surplus rises. Government revenue = t * Q_imports. DWL = two triangles (production inefficiency + consumption inefficiency). Net welfare effect: CS_loss > PS_gain + revenue --> DWL > 0 for small country. Quota Q_max: same price/quantity effect as a tariff but revenue accrues to quota holders, not government.
  - Depends: DEF-CHO003 (comparative advantage -- trade policy restricts gains from comparative advantage), PRIM-MKT003 (equilibrium reasoning -- trade policy shifts domestic equilibrium), DEF-MKT005 (deadweight loss -- trade restrictions create DWL)
  - Ownership: POL
  - Source: SRC-GLB001 (OpenStax Ch. 33--34), SRC-GLB002 (Mankiw Ch. 9)
  - Referenced by: ---
  - Tier: E
  - Real-world hook: In 2018, the US imposed tariffs on imported steel (25%) and aluminum (10%). American steel producers benefited (higher prices, more domestic production). But American car manufacturers, construction companies, and appliance makers faced higher input costs. Economists estimated the tariffs cost consumers about $900,000 per steel job saved. Trade policy reasoning weighs the concentrated benefits (steel workers) against the diffuse costs (all consumers of steel-containing products).

## 5. Axioms

- AX-POL001: **Efficiency-equity tradeoff**
  - Statement: Policies that increase economic efficiency (maximize total surplus) may worsen equity (fairness of distribution), and policies that improve equity may reduce efficiency. There is no policy that costlessly improves both.
  - Description: This axiom formalizes the fundamental tension in policy analysis. A competitive market maximizes total surplus (efficiency), but the resulting distribution may be very unequal. Redistributive policies (progressive taxation, welfare programs) improve equity but create distortions that reduce efficiency (taxes create deadweight loss, welfare can reduce work incentives). The tradeoff is not absolute -- well-designed policies can minimize efficiency costs -- but it cannot be eliminated entirely. This axiom ensures that students evaluate policies on both dimensions rather than optimizing on one and ignoring the other.
  - Depends: none (axiom -- taken as given; it is a normative principle, not derivable from positive economics alone)
  - Ownership: POL
  - Source: SRC-POL003 (Okun 1975), SRC-GLB002 (Mankiw Ch. 1, Ten Principles)
  - Referenced by: ---
  - Tier: C
  - Normative: MUST (all policy analysis in the taxonomy must acknowledge both efficiency and equity dimensions)
  - Real-world hook: A flat tax (everyone pays the same rate) is efficient (minimizes distortions) but inequitable (the poor pay a larger share of their income). A progressive tax (higher rates on higher incomes) is more equitable but less efficient (higher rates create larger distortions). There is no tax system that is both perfectly efficient and perfectly equitable. Policy reasoning requires navigating this tradeoff, not pretending it does not exist.

- AX-POL002: **No free lunch in policy**
  - Statement: Every policy intervention has costs (direct fiscal costs, distorted incentives, administrative burden, unintended consequences). The question is never "does this policy have costs?" but "do the benefits exceed the costs?"
  - Description: This axiom is the policy-level extension of scarcity reasoning: just as individuals face tradeoffs, governments face tradeoffs. There is no policy that produces only benefits with no costs. Subsidies must be funded (opportunity cost of the tax revenue). Regulations impose compliance costs. Transfer programs may reduce work incentives. Even "free" government services are funded by taxes that create deadweight loss. This axiom inoculates against two equal and opposite errors: (1) rejecting all government action because it has costs (every action has costs -- including inaction); (2) endorsing government action without counting costs (benefits are visible; costs are often hidden or diffuse).
  - Depends: none (axiom -- foundational principle of policy analysis)
  - Ownership: POL
  - Source: SRC-GLB002 (Mankiw Ch. 1, "There is no such thing as a free lunch"), SRC-POL002 (Musgrave 1959)
  - Referenced by: ---
  - Tier: C
  - Normative: MUST (all policy analysis in the taxonomy must identify both benefits and costs)
  - Real-world hook: "Free college" is not free. Someone pays -- taxpayers. The question is not whether free college has costs (it does: roughly $80 billion per year in the US) but whether the benefits (more educated workforce, reduced student debt, greater social mobility) exceed those costs. Policy reasoning demands identifying the costs, not assuming they do not exist.

## 6. Contested Concepts

| Concept | POL Version (Owner) | Other Domain Version | Resolution |
|---------|---------------------|----------------------|------------|
| Market failure correction | PRIM-POL001 (prescription: how to fix) | MKT provides diagnosis (DEF-MKT006, DEF-MKT007) | Clean split per P5: MKT identifies the failure; POL designs the intervention |
| Monetary policy | PRIM-POL003 (when/why to deploy) | MON provides the tools (DEF-MON003) | Clean split per P5: MON describes mechanism; POL describes deployment strategy |
| Fiscal policy | PRIM-POL002 (when/why to deploy) | MAC provides the framework (DEF-MAC002, DEF-MAC003) | Clean split per P5: MAC describes the aggregate model; POL uses it for policy decisions |
| Tax | DEF-POL002 (tax incidence: who bears the burden) | MKT provides elasticity framework (PRIM-MKT004) | POL owns the policy analysis; MKT provides the analytical tools POL imports |

## 7. Real-World Hooks

| ID | Concept | Everyday Application |
|----|---------|---------------------|
| PRIM-POL001 | Market failure correction | A carbon tax on gasoline: makes drivers face the true social cost of driving, including climate damage |
| PRIM-POL002 | Fiscal policy reasoning | COVID stimulus: $5 trillion in spending reduced unemployment from 14.7% to 3.5%, but contributed to 9% inflation |
| PRIM-POL003 | Monetary policy reasoning | Fed raised rates from 0% to 5%+ in 2022-23 to fight inflation: mortgage rates doubled, borrowing slowed |
| DEF-POL001 | Government budget and deficit | US debt at $34 trillion: scary as a raw number, more manageable when compared to GDP (120% ratio) |
| DEF-POL002 | Tax incidence | The 1990 yacht luxury tax: intended to burden the rich, actually devastated boat builders |
| DEF-POL003 | Trade policy | 2018 steel tariffs: saved steel jobs at $900,000 per job, paid by all consumers of steel products |
| AX-POL001 | Efficiency-equity tradeoff | Flat tax vs. progressive tax: no system is both perfectly efficient and perfectly fair |
| AX-POL002 | No free lunch in policy | "Free college" costs ~$80 billion/year; the question is whether benefits exceed those costs |

## 8. Intra-Domain Dependency Graph

```
PRIM-POL001 (Market failure correction reasoning)
     [depends on DEF-MKT006, DEF-MKT005, PRIM-CHO004]

PRIM-POL002 (Fiscal policy reasoning)
     [depends on DEF-MAC002, PRIM-MAC005, PRIM-CHO002]
     |
     +---> DEF-POL001 (Government budget and deficit)
              [also depends on PRIM-CHO001]

PRIM-POL003 (Monetary policy reasoning)
     [depends on DEF-MON003, PRIM-MON003, DEF-MAC002, PRIM-MAC003]

DEF-POL002 (Tax incidence)
     [depends on PRIM-MKT004, PRIM-MKT003, DEF-MKT005]

DEF-POL003 (Trade policy) [E]
     [depends on DEF-CHO003, PRIM-MKT003, DEF-MKT005]

AX-POL001 (Efficiency-equity tradeoff)
     [independent -- axiom]

AX-POL002 (No free lunch in policy)
     [independent -- axiom]
```

**Acyclicity verification**: POL items depend only on items from upstream domains (CHO, MKT, MAC, MON) or on other POL items listed earlier. PRIM-POL001, PRIM-POL002, PRIM-POL003, DEF-POL002, and the two axioms have no intra-domain forward dependencies. DEF-POL001 depends on PRIM-POL002 (listed earlier). DEF-POL003 depends only on cross-domain imports. No cycles exist. The graph is a DAG.

**Core-only subgraph**: Removing DEF-POL003 (E) leaves all Core items with satisfied dependencies. No Core item depends on DEF-POL003.

## 9. Cross-Domain Interface

### Exports

POL is the terminal domain. No other domain imports from POL. POL exports nothing.

| ID | Concept | Imported by |
|----|---------|-------------|
| (none) | --- | --- |

### Imports

| DEP ID | Imported Item | From Domain | Used by |
|--------|---------------|-------------|---------|
| DEP-POL001 | PRIM-CHO001 | CHO | DEF-POL001 (government budget = scarcity) |
| DEP-POL002 | PRIM-CHO002 | CHO | PRIM-POL002 (fiscal policy involves OC) |
| DEP-POL003 | PRIM-CHO003 | CHO | Optimal policy uses marginal analysis |
| DEP-POL004 | PRIM-CHO004 | CHO | PRIM-POL001 (market correction via incentives) |
| DEP-POL005 | AX-CHO001 | CHO | Policy analysis assumes rational agent responses |
| DEP-POL006 | PRIM-MKT003 | MKT | DEF-POL002 (tax incidence uses equilibrium) |
| DEP-POL007 | PRIM-MKT004 | MKT | DEF-POL002 (tax burden depends on elasticity) |
| DEP-POL008 | PRIM-MKT005 | MKT | Antitrust and regulation analysis |
| DEP-POL009 | DEF-MKT003 | MKT | Price controls as policy tools |
| DEP-POL010 | DEF-MKT004 | MKT | Welfare analysis uses surplus |
| DEP-POL011 | DEF-MKT005 | MKT | Policy-induced DWL |
| DEP-POL012 | DEF-MKT006 | MKT | PRIM-POL001 (externality correction) |
| DEP-POL013 | DEF-MKT007 | MKT | PRIM-POL001 (public good provision) |
| DEP-POL014 | PRIM-MAC001 | MAC | Fiscal/monetary policy targets |
| DEP-POL015 | PRIM-MAC002 | MAC | Unemployment target |
| DEP-POL016 | PRIM-MAC003 | MAC | Inflation target |
| DEP-POL017 | PRIM-MAC005 | MAC | Business cycle triggers fiscal response |
| DEP-POL018 | DEF-MAC002 | MAC | Fiscal/monetary policy shifts AD |
| DEP-POL019 | DEF-MAC003 | MAC | Supply-side policy shifts AS |
| DEP-POL020 | PRIM-MON003 | MON | Monetary policy channel |
| DEP-POL021 | PRIM-MON004 | MON | Money supply target |
| DEP-POL022 | DEF-MON003 | MON | Monetary policy tools |

## 10. Difficulty Tiers

| ID | Concept | Tier | Justification |
|----|---------|------|---------------|
| PRIM-POL001 | Market failure correction reasoning | C | Core: the foundational microeconomic rationale for government intervention |
| PRIM-POL002 | Fiscal policy reasoning | C | Core: the primary macro-level government spending/tax tool; essential for evaluating budget debates |
| PRIM-POL003 | Monetary policy reasoning | C | Core: the primary macro-level central bank tool; essential for understanding Fed decisions |
| DEF-POL001 | Government budget and deficit | C | Core: connects fiscal policy to long-run fiscal sustainability; essential for debt discussions |
| DEF-POL002 | Tax incidence | C | Core: the deeply counterintuitive result that legal tax assignment does not determine economic burden |
| DEF-POL003 | Trade policy | E | Enrichment: important for globalization debates but not required by Core downstream items |
| AX-POL001 | Efficiency-equity tradeoff | C | Core axiom: without it, students optimize policy on one dimension and ignore the other |
| AX-POL002 | No free lunch in policy | C | Core axiom: without it, students evaluate policies by benefits alone, ignoring costs |

**Tier constraint verification**: The sole Enrichment item is DEF-POL003 (Trade policy). No Core item depends on DEF-POL003. The 7 Core items form a self-contained, dependency-complete sub-taxonomy.

## 11. Self-Audit Checklist

- [x] Every PRIM has: reasoning move formulation, description, semi-formal statement, depends, ownership, source, referenced-by, tier, real-world hook
- [x] Every DEF depends only on previously listed PRIM/DEF or cross-domain imports (verified via dependency graph)
- [x] Every cross-domain reference uses full `{Type}-{Code}{Number}` format
- [x] Every import is listed in the respective source domain's exports (all 22 DEP items verified)
- [x] Dissolution argument is present and non-trivial (multiple sentences; normative dimension unique to POL; intention-outcome gap)
- [x] Real-world hooks cover everyday non-major contexts (carbon tax, COVID stimulus, Fed rate hikes, national debt, yacht tax, steel tariffs, flat vs. progressive tax, free college)
- [x] Intra-domain dependency graph is acyclic (all items depend only on earlier POL items or cross-domain imports)
- [x] Tier annotations (C/E) are present on all 8 items
- [x] No PRIM/DEF duplicates an entry in another domain (checked against Primitive Registry)
- [x] Reasoning moves are genuinely "Given X, do Y" cognitive operations
