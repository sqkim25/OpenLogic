# DOMAIN-MKT v0.1

## 0. Sources & Assumptions

- SRC-MKT001: Colander, *Economics*, 11th ed., 2020, Ch. 3--8 (supply, demand, elasticity, market structures)
- SRC-MKT002: Marshall, *Principles of Economics*, 1890 (original supply-demand framework; scissors analogy)
- SRC-MKT003: Kahneman, Knetsch, & Thaler, "Anomalies: The Endowment Effect, Loss Aversion, and Status Quo Bias," *Journal of Economic Perspectives*, 1991 (market anomalies that qualify the competitive model)
- SRC-GLB001: OpenStax, *Principles of Economics*, 3rd ed., 2023, Ch. 3--8, 9--11
- SRC-GLB002: Mankiw, *Principles of Economics*, 9th ed., 2021, Ch. 4--7, 14--17
- SRC-GLB003: CORE Econ, *The Economy*, 2017, Unit 8 (supply and demand), Unit 7 (firm behavior)
- ASM-MKT001: Markets are analyzed graphically using supply and demand curves. No calculus-based optimization. Justification: the graphical approach is the standard for introductory courses and is sufficient for all Core-tier reasoning moves (ASM-GLB002).
- ASM-MKT002: Perfect competition is the baseline model. Monopoly, oligopoly, and monopolistic competition are presented as deviations from the competitive benchmark. Justification: starting with the simplest market structure builds intuition before introducing complexity; this is the standard pedagogical sequence (SRC-GLB001, SRC-GLB002).

## 1. Domain Intent

- **Governing question**: How do prices coordinate decisions?
- **Scope**: The mechanisms by which individual buying and selling decisions aggregate into market outcomes. This includes demand and supply analysis, equilibrium determination, elasticity, efficiency (surplus analysis), market structures (perfect competition, monopoly, oligopoly, monopolistic competition), and market failures (externalities, public goods). MKT provides the coordination layer: how the interaction of many agents through prices produces an allocation of resources.
- **Non-goals**: Why individual agents decide the way they do (CHO -- that is the decision logic). Economy-wide aggregates like GDP, unemployment, or the general price level (MAC). How the banking system creates money or sets interest rates (MON). What specific policies governments should adopt to fix market failures (POL -- MKT identifies the failures; POL designs the interventions).
- **Dissolution argument**: Markets answer HOW prices coordinate millions of independent decisions. Choice answers HOW individuals decide. You can analyze a single person's opportunity cost without ever drawing a supply-demand diagram; conversely, you can analyze market equilibrium without understanding the psychological detail of how each buyer formed their preferences. MKT takes individual decision-making as an input (agents have preferences, constraints, and respond to incentives) and studies the emergent outcome when many such agents interact. Merging MKT into CHO would lose the coordination mechanism -- the fact that a price emerges from collective interaction that no single agent controls. Merging MKT into MAC would conflate the analysis of one market (wheat, labor, housing) with the analysis of the entire economy; microeconomic market analysis is possible without any reference to GDP or national unemployment.
- **Threshold schema mapping**: Partial --> General. The foundational conceptual shift in MKT is recognizing that everything is connected through prices: a change in one market ripples through others. A drought that raises corn prices also raises beef prices (corn feeds cattle), gasoline prices (corn-based ethanol), and food prices generally. Students who fail to cross this threshold treat each market as isolated.

## 2. Prerequisites

MKT depends on CHO and imports the following:

| DEP ID | Imported Item | Reason |
|--------|---------------|--------|
| DEP-MKT001 | PRIM-CHO001 (Scarcity reasoning) | Markets exist because scarcity forces allocation; without scarcity, there is no need for price coordination |
| DEP-MKT002 | PRIM-CHO002 (Opportunity cost reasoning) | Supply curves reflect opportunity costs of production; the decision to buy reflects the opportunity cost of spending money |
| DEP-MKT003 | PRIM-CHO003 (Marginal analysis) | Demand curves reflect diminishing marginal benefit; supply curves reflect rising marginal cost; equilibrium is where MB = MC for the market |
| DEP-MKT004 | PRIM-CHO004 (Incentive reasoning) | Demand and supply shifts are driven by changed incentives; agents respond to price changes as incentive signals |
| DEP-MKT005 | DEF-CHO002 (Diminishing marginal returns) | Rising marginal cost (upward-sloping supply) is a consequence of diminishing marginal returns in production |
| DEP-MKT006 | AX-CHO001 (Rational self-interest) | Supply and demand presuppose that buyers maximize benefit and sellers maximize profit |

MKT does NOT depend on MAC, MON, or POL:
- **MKT does not depend on MAC**: Individual markets operate without reference to GDP, national unemployment, or the aggregate price level. The wheat market clears based on wheat-specific supply and demand, not macroeconomic conditions.
- **MKT does not depend on MON**: Markets can be analyzed in terms of relative prices (barter ratios) without money. The supply-demand framework predates any monetary theory.
- **MKT does not depend on POL**: Markets exist in the absence of government intervention. POL describes deviations from and corrections to market outcomes, but the market mechanism itself requires no policy inputs.

## 3. Primitives

- PRIM-MKT001: **Demand reasoning**
  - Reasoning move: Given a change in the price of a good or a change in a non-price factor (income, preferences, prices of related goods, expectations, population), determine the direction and nature of the effect on the quantity demanded or the position of the demand curve.
  - Description: The cognitive operation of predicting buyer behavior in aggregate. Demand reasoning has two layers: (1) the law of demand -- when the price of a good rises and all else is equal, quantity demanded falls (movement along the demand curve); (2) demand shifters -- non-price factors that change the entire demand curve's position. Demand reasoning imports marginal analysis from CHO: the demand curve reflects diminishing marginal benefit (consumers value additional units less). The key distinction is between a change in quantity demanded (price change, movement along the curve) and a change in demand (shifter, the whole curve moves). Students who conflate these two make systematic errors in market analysis.
  - Semi-formal: Demand function: Q_d = f(P, income, preferences, P_substitutes, P_complements, expectations, population). Law of demand: dQ_d/dP < 0 (negative relationship). Demand curve shift: any change in a non-price determinant shifts Q_d at every price level. Movement along curve: only price changes cause movement along a fixed demand curve.
  - Depends: PRIM-CHO003 (marginal analysis -- demand curve reflects diminishing marginal benefit), PRIM-CHO004 (incentive reasoning -- demand responds to price incentives), AX-CHO001 (rational self-interest -- consumers maximize utility)
  - Ownership: MKT
  - Source: SRC-GLB001 (OpenStax Ch. 3), SRC-GLB002 (Mankiw Ch. 4), SRC-MKT002 (Marshall 1890)
  - Referenced by: MAC, POL
  - Tier: C
  - Real-world hook: When avocado prices spike, you buy fewer avocados (movement along the demand curve -- law of demand). When a celebrity promotes a new superfood, demand for that food increases even at the same price (shift in the demand curve -- preferences changed). Understanding which type of change occurred is the first step in predicting market outcomes.

- PRIM-MKT002: **Supply reasoning**
  - Reasoning move: Given a change in the price of a good or a change in a non-price factor (input costs, technology, number of sellers, expectations, regulation), determine the direction and nature of the effect on the quantity supplied or the position of the supply curve.
  - Description: The cognitive operation of predicting seller behavior in aggregate. Supply reasoning mirrors demand reasoning for the production side: (1) the law of supply -- when the price rises, quantity supplied increases (movement along the supply curve); (2) supply shifters -- non-price factors that change the entire curve. The upward slope of the supply curve reflects rising marginal cost from diminishing marginal returns (DEF-CHO002). As with demand, the critical distinction is between movement along the curve (price change) and shift of the curve (non-price factor change).
  - Semi-formal: Supply function: Q_s = f(P, input_costs, technology, num_sellers, expectations, regulation). Law of supply: dQ_s/dP > 0 (positive relationship). Supply curve shift: any change in a non-price determinant shifts Q_s at every price level. Movement along curve: only price changes cause movement along a fixed supply curve.
  - Depends: PRIM-CHO003 (marginal analysis -- supply curve reflects rising marginal cost), DEF-CHO002 (diminishing marginal returns -- explains why marginal cost rises), AX-CHO001 (rational self-interest -- firms maximize profit)
  - Ownership: MKT
  - Source: SRC-GLB001 (OpenStax Ch. 3), SRC-GLB002 (Mankiw Ch. 4), SRC-MKT002 (Marshall 1890)
  - Referenced by: MAC, POL
  - Tier: C
  - Real-world hook: When the price of coffee beans rises, farmers plant more coffee trees (movement along supply curve). When a new harvesting machine cuts production costs, farmers can offer more coffee at every price (supply curve shifts right -- technology improvement). When a drought destroys crops, supply shifts left (input -- arable land -- became scarce).

- PRIM-MKT003: **Equilibrium reasoning**
  - Reasoning move: Given a supply curve and a demand curve for a market, find the price and quantity where the two curves intersect, then predict what happens when supply or demand shifts by tracing through to the new equilibrium.
  - Description: The cognitive operation of finding where markets clear. At the equilibrium price, quantity demanded equals quantity supplied -- there is no shortage and no surplus. If the price is above equilibrium, surplus exists (Q_s > Q_d), pushing the price down. If below, shortage exists (Q_d > Q_s), pushing the price up. The market naturally moves toward equilibrium through the self-correcting mechanism of price adjustment. Equilibrium reasoning is the central analytical tool of microeconomics: almost every market question reduces to "what happened to supply and/or demand, and where is the new equilibrium?" This is Marshall's "scissors" -- neither blade alone cuts; supply and demand together determine price.
  - Semi-formal: Equilibrium: P* and Q* such that Q_d(P*) = Q_s(P*). If P > P*: surplus = Q_s(P) - Q_d(P) > 0; price falls. If P < P*: shortage = Q_d(P) - Q_s(P) > 0; price rises. Comparative statics: if demand shifts right (increase), new equilibrium has higher P* and higher Q*. If supply shifts right (increase), new equilibrium has lower P* and higher Q*. Simultaneous shifts require knowing relative magnitudes.
  - Depends: PRIM-MKT001 (demand reasoning -- need the demand curve), PRIM-MKT002 (supply reasoning -- need the supply curve)
  - Ownership: MKT
  - Source: SRC-GLB001 (OpenStax Ch. 3), SRC-GLB002 (Mankiw Ch. 4), SRC-MKT002 (Marshall 1890)
  - Referenced by: MAC, POL
  - Tier: C
  - Real-world hook: In 2021, a semiconductor shortage (supply shift left) coincided with increased remote-work demand for electronics (demand shift right). Equilibrium reasoning predicts: price of electronics rises dramatically, which is exactly what happened. Every "why did the price of X go up/down?" question in the news is an equilibrium reasoning question.

- PRIM-MKT004: **Elasticity reasoning**
  - Reasoning move: Given a percentage change in price (or income), determine the percentage change in quantity demanded or supplied, and classify the responsiveness as elastic, inelastic, or unit-elastic to predict revenue effects and policy impacts.
  - Description: The cognitive operation of measuring how responsive buyers or sellers are to price changes. Knowing that "demand falls when price rises" is not enough -- you need to know by HOW MUCH. Elasticity answers this question. If demand is elastic (|E_d| > 1), a price increase causes a proportionally larger drop in quantity, so total revenue falls. If inelastic (|E_d| < 1), quantity drops less than proportionally, so total revenue rises. Elasticity determines who bears the burden of a tax, whether a price increase helps or hurts sellers' revenue, and how effective price controls are. The key determinants of demand elasticity are: availability of substitutes, necessity vs. luxury, fraction of budget, and time horizon.
  - Semi-formal: Price elasticity of demand: E_d = (%change in Q_d) / (%change in P). |E_d| > 1: elastic (quantity very responsive). |E_d| < 1: inelastic (quantity less responsive). |E_d| = 1: unit-elastic. Revenue effect: if elastic, P increase causes revenue to fall (quantity effect dominates). If inelastic, P increase causes revenue to rise (price effect dominates). Similarly, price elasticity of supply: E_s = (%change in Q_s) / (%change in P).
  - Depends: PRIM-MKT001 (demand reasoning -- elasticity measures the responsiveness embedded in the demand curve), PRIM-MKT002 (supply reasoning -- supply elasticity measures seller responsiveness)
  - Ownership: MKT
  - Source: SRC-GLB001 (OpenStax Ch. 5), SRC-GLB002 (Mankiw Ch. 5), SRC-GLB005 (Davies & Mangan 2007, threshold concept)
  - Referenced by: POL
  - Tier: C
  - Real-world hook: When OPEC cuts oil production, gas prices rise. But people still need to drive to work -- gas demand is inelastic in the short run. So OPEC earns more revenue despite selling less oil. If demand were elastic (like for vacation travel), the price increase would drive away so many buyers that revenue would fall. Elasticity explains why OPEC targets oil, not beach towels.

- PRIM-MKT005: **Market structure reasoning**
  - Reasoning move: Given information about the number of sellers, product differentiation, entry barriers, and pricing power in an industry, classify the market structure and predict how firms in that structure set prices and quantities compared to the competitive benchmark.
  - Description: The cognitive operation of recognizing that not all markets look like the perfectly competitive ideal. Market structure reasoning classifies industries into four types: (1) perfect competition -- many sellers, identical products, no barriers, no pricing power (agriculture); (2) monopolistic competition -- many sellers, differentiated products, low barriers, some pricing power (restaurants); (3) oligopoly -- few sellers, significant barriers, strategic interdependence (airlines); (4) monopoly -- one seller, high barriers, full pricing power (local utility). The key insight is that as market power increases (from competition toward monopoly), price rises above marginal cost, output falls below the efficient level, and deadweight loss emerges. Market structure determines how well the "invisible hand" works.
  - Semi-formal: Market structure classification based on: N (number of sellers), D (product differentiation), B (barriers to entry), P (pricing power). Perfect competition: N = many, D = none, B = none, P = none; P = MC. Monopoly: N = 1, B = high, P = full; P > MC, deadweight loss > 0. Oligopoly: N = few, B = moderate-high, strategic interaction. Monopolistic competition: N = many, D = yes, B = low, P = limited; P > MC in short run.
  - Depends: PRIM-MKT003 (equilibrium reasoning -- market structure determines how equilibrium is reached), PRIM-CHO003 (marginal analysis -- all market structures involve comparing marginal revenue and marginal cost)
  - Ownership: MKT
  - Source: SRC-GLB001 (OpenStax Ch. 8--11), SRC-GLB002 (Mankiw Ch. 14--17)
  - Referenced by: POL
  - Tier: C
  - Real-world hook: Why is your cell phone plan so expensive compared to what it would cost in a perfectly competitive market? Because the wireless industry is an oligopoly: only a few carriers (high barriers -- spectrum licenses cost billions), strategic pricing, and product differentiation. Market structure reasoning explains why some industries charge high prices while others compete prices down to cost.

## 4. Definitions

- DEF-MKT001: **Demand curve**
  - Reasoning move: Given a set of price-quantity pairs representing buyers' willingness to pay, construct the demand curve and read it to determine quantity demanded at any given price, or the maximum price consumers will pay for any given quantity.
  - Description: The demand curve is the graphical representation of demand reasoning. It plots price on the vertical axis and quantity on the horizontal axis, showing the inverse relationship between price and quantity demanded. The curve can be read two ways: horizontally (at price P, how much will consumers buy?) and vertically (for the Q-th unit, what is the maximum a consumer will pay? -- this is the marginal benefit). The area under the demand curve above the price represents consumer surplus. The demand curve operationalizes the abstract law of demand into a visual tool for analysis.
  - Semi-formal: D: P --> Q_d, a function (usually downward-sloping) mapping each price to a quantity demanded. Graphically: vertical axis = P, horizontal axis = Q. Movement along D: price change. Shift of D: non-price factor change. Consumer surplus = integral from 0 to Q* of [D(Q) - P*] dQ (area between demand curve and price line).
  - Depends: PRIM-MKT001 (demand reasoning -- the demand curve is the graphical representation of demand)
  - Ownership: MKT
  - Source: SRC-GLB001 (OpenStax Ch. 3), SRC-GLB002 (Mankiw Ch. 4)
  - Referenced by: MAC
  - Tier: C
  - Real-world hook: When a concert sells out instantly, the demand curve tells you the market-clearing price is above the ticket price. If tickets were priced where the demand curve intersects the supply (venue capacity), there would be no scalpers.

- DEF-MKT002: **Supply curve**
  - Reasoning move: Given a set of price-quantity pairs representing sellers' costs of production, construct the supply curve and read it to determine quantity supplied at any given price, or the minimum price sellers need to produce any given quantity.
  - Description: The supply curve is the graphical representation of supply reasoning. It plots price on the vertical axis and quantity on the horizontal axis, showing the positive relationship between price and quantity supplied. The curve can be read vertically as the marginal cost curve: for the Q-th unit, what is the minimum price a seller needs to cover the cost of producing it? The area above the supply curve below the price represents producer surplus. The supply curve's upward slope reflects diminishing marginal returns in production.
  - Semi-formal: S: P --> Q_s, a function (usually upward-sloping) mapping each price to a quantity supplied. Graphically: vertical axis = P, horizontal axis = Q. Movement along S: price change. Shift of S: non-price factor change. Producer surplus = integral from 0 to Q* of [P* - S(Q)] dQ (area between price line and supply curve).
  - Depends: PRIM-MKT002 (supply reasoning -- the supply curve is the graphical representation of supply)
  - Ownership: MKT
  - Source: SRC-GLB001 (OpenStax Ch. 3), SRC-GLB002 (Mankiw Ch. 4)
  - Referenced by: MAC
  - Tier: C
  - Real-world hook: The supply curve for housing in San Francisco is nearly vertical (inelastic) because geography and zoning severely limit new construction. That is why increased demand does not lead to much new housing -- it leads mainly to higher prices.

- DEF-MKT003: **Price ceiling and floor**
  - Reasoning move: Given a government-imposed price that differs from market equilibrium, determine whether the result is a shortage (ceiling below equilibrium) or surplus (floor above equilibrium), and identify the efficiency consequences.
  - Description: A price ceiling is a legal maximum price (cannot charge more). A price floor is a legal minimum price (cannot charge less). When binding (set away from equilibrium in the restricting direction), these controls prevent the market from reaching equilibrium. A ceiling below equilibrium creates a shortage (Q_d > Q_s at the ceiling price), leading to rationing, waiting lines, or black markets. A floor above equilibrium creates a surplus (Q_s > Q_d at the floor price), leading to unsold goods or unemployment (in the case of minimum wage as a labor market floor). Price controls are the simplest example of government interference with market equilibrium.
  - Semi-formal: Price ceiling P_c: if P_c < P*, then Q_d(P_c) > Q_s(P_c); shortage = Q_d(P_c) - Q_s(P_c) > 0. Price floor P_f: if P_f > P*, then Q_s(P_f) > Q_d(P_f); surplus = Q_s(P_f) - Q_d(P_f) > 0. A non-binding ceiling (P_c > P*) or floor (P_f < P*) has no effect.
  - Depends: PRIM-MKT003 (equilibrium reasoning -- price controls are deviations from equilibrium)
  - Ownership: MKT
  - Source: SRC-GLB001 (OpenStax Ch. 3), SRC-GLB002 (Mankiw Ch. 6)
  - Referenced by: POL
  - Tier: C
  - Real-world hook: Rent control in New York City is a price ceiling: maximum rents are set below market equilibrium, creating a chronic housing shortage. The minimum wage is a price floor in the labor market: if set above the equilibrium wage, it creates a surplus of labor (unemployment among low-skill workers). In both cases, the price control prevents the market from clearing.

- DEF-MKT004: **Consumer and producer surplus**
  - Reasoning move: Given a supply-demand diagram with an equilibrium price, compute the areas representing consumer surplus (benefit buyers receive above what they pay) and producer surplus (benefit sellers receive above their cost) to measure market welfare.
  - Description: Consumer surplus is the difference between what consumers are willing to pay and what they actually pay, summed over all units purchased. Producer surplus is the difference between the price received and the minimum price sellers would accept, summed over all units sold. Total surplus = consumer surplus + producer surplus. This is the standard welfare measure in economics: a market outcome is efficient when it maximizes total surplus. Any deviation from the competitive equilibrium (due to taxes, price controls, monopoly power, or externalities) reduces total surplus, creating deadweight loss.
  - Semi-formal: Consumer surplus CS = sum over all buyers of (willingness to pay - price paid) = area below demand curve, above P*, from 0 to Q*. Producer surplus PS = sum over all sellers of (price received - minimum acceptable price) = area above supply curve, below P*, from 0 to Q*. Total surplus TS = CS + PS. At competitive equilibrium, TS is maximized.
  - Depends: DEF-MKT001 (demand curve -- CS is the area under the demand curve above price), DEF-MKT002 (supply curve -- PS is the area above the supply curve below price), PRIM-MKT003 (equilibrium reasoning -- surplus is computed at equilibrium)
  - Ownership: MKT
  - Source: SRC-GLB001 (OpenStax Ch. 3), SRC-GLB002 (Mankiw Ch. 7)
  - Referenced by: POL
  - Tier: C
  - Real-world hook: When you buy a used textbook for $20 that you were willing to pay $50 for, your consumer surplus on that transaction is $30. When the seller accepts $20 but would have accepted as low as $10, the seller's producer surplus is $10. The $40 of total surplus is the gain from this voluntary trade. Markets generate surplus -- that is why voluntary exchange makes both sides better off.

- DEF-MKT005: **Deadweight loss**
  - Reasoning move: Given a market distortion (tax, price control, monopoly, externality), identify the transactions that would have occurred at the competitive equilibrium but do not occur under the distortion, and quantify the resulting loss of total surplus.
  - Description: Deadweight loss is the reduction in total surplus caused by a market distortion. It represents mutually beneficial trades that do not happen because the distortion has driven a wedge between the price buyers pay and the price sellers receive (or between marginal benefit and marginal cost). Deadweight loss is a pure loss -- it does not become someone else's gain; it simply vanishes. A tax creates deadweight loss because some transactions whose value exceeds their cost are blocked by the tax wedge. A monopoly creates deadweight loss because the monopolist restricts output to raise price. Deadweight loss is the efficiency argument against market distortions.
  - Semi-formal: At competitive equilibrium, TS = CS + PS (maximized). With distortion, TS' = CS' + PS' + government revenue (if tax). Deadweight loss DWL = TS - TS' > 0. Graphically, DWL is the triangle between the supply and demand curves, from Q_distorted to Q*. DWL increases with the square of the distortion (doubling the tax quadruples the DWL).
  - Depends: DEF-MKT004 (consumer and producer surplus -- deadweight loss is the reduction in total surplus), PRIM-MKT003 (equilibrium reasoning -- deadweight loss is measured relative to the competitive equilibrium)
  - Ownership: MKT
  - Source: SRC-GLB001 (OpenStax Ch. 3, 12), SRC-GLB002 (Mankiw Ch. 8)
  - Referenced by: POL
  - Tier: C
  - Real-world hook: A tax on sugary drinks raises the price. Some consumers who valued the drink more than its production cost now do not buy it because the tax pushes the total price above their willingness to pay. That lost transaction is deadweight loss -- neither the consumer, the producer, nor the government captured that value. It simply disappeared.

- DEF-MKT006: **Externality**
  - Reasoning move: Given an economic activity that affects a third party not involved in the transaction, identify whether the external effect is positive (benefit) or negative (cost), determine how it causes the market to over- or under-produce the good, and explain why the market equilibrium is inefficient.
  - Description: An externality exists when the production or consumption of a good imposes costs (negative externality) or benefits (positive externality) on third parties who are not compensated or charged. Pollution is the classic negative externality: a factory's production imposes costs on nearby residents (health, property values) that are not reflected in the factory's costs or the product's price. Education is a classic positive externality: an educated person benefits not just themselves but society (lower crime, better citizenship, innovation). The market fails because prices do not capture the full social cost or benefit: with a negative externality, the market overproduces (social cost > private cost); with a positive externality, the market underproduces (social benefit > private benefit).
  - Semi-formal: Negative externality: social cost = private cost + external cost. Market produces where private MC = MB, but efficiency requires social MC = MB. Since social MC > private MC, market output Q_market > Q_efficient. Positive externality: social benefit = private benefit + external benefit. Market produces where private MB = MC, but efficiency requires social MB = MC. Since social MB > private MB, market output Q_market < Q_efficient.
  - Depends: PRIM-MKT003 (equilibrium reasoning -- externalities cause the market equilibrium to be inefficient), DEF-MKT005 (deadweight loss -- externalities create DWL by causing over- or underproduction)
  - Ownership: MKT
  - Source: SRC-GLB001 (OpenStax Ch. 12), SRC-GLB002 (Mankiw Ch. 10)
  - Referenced by: POL
  - Tier: C
  - Real-world hook: When a factory emits pollution, nearby residents bear the health costs but the factory does not pay for them. The product is priced too low (it does not include the pollution cost), so the market produces too much of it. This is why economists argue for pollution taxes or cap-and-trade: to force the price to reflect the true social cost.

- DEF-MKT007: **Public good**
  - Reasoning move: Given a good or service, determine whether it is non-excludable (cannot prevent non-payers from using it) and non-rivalrous (one person's use does not reduce another's), and if so, explain why the market will undersupply it (the free-rider problem).
  - Description: A public good has two defining properties: non-excludability (you cannot prevent anyone from consuming it) and non-rivalry (one person's consumption does not diminish another's). National defense is the classic example: it protects everyone in the country whether or not they pay taxes, and one person being protected does not reduce the protection available to others. The problem is that rational agents have an incentive to free-ride -- enjoy the good without paying -- because they cannot be excluded. If everyone free-rides, the good is not produced at all, even though everyone would benefit. This is why public goods are typically provided by governments, funded through taxation.
  - Semi-formal: Good G is a public good iff: (1) non-excludable: if G is provided, all agents can consume G regardless of payment; (2) non-rivalrous: consumption by agent i does not reduce availability to agent j. Free-rider problem: each agent's optimal strategy is to not pay (consume for free). If all agents free-ride, G is not provided. Market failure: Q_market = 0 or Q_market << Q_efficient.
  - Depends: PRIM-CHO004 (incentive reasoning -- the free-rider problem arises because agents have incentives to not pay), DEF-MKT006 (externality -- public goods are a special case of positive externality where the external benefit is the entire benefit)
  - Ownership: MKT
  - Source: SRC-GLB001 (OpenStax Ch. 13), SRC-GLB002 (Mankiw Ch. 11)
  - Referenced by: POL
  - Tier: E
  - Real-world hook: A lighthouse benefits all passing ships whether or not their owners paid for it -- it is non-excludable. One ship seeing the light does not dim it for another -- it is non-rivalrous. If you asked each ship owner to voluntarily pay for the lighthouse, most would free-ride, hoping someone else pays. That is why lighthouses are publicly funded.

## 5. Contested Concepts

The primary contested boundary for MKT is with POL. Four concepts require explicit ownership resolution:

| Concept | MKT Version (Owner) | POL Version (Owner) | Resolution |
|---------|---------------------|---------------------|------------|
| Externality | DEF-MKT006 (market failure diagnosis -- what it is, why it causes inefficiency) | PRIM-POL001 (market failure correction -- how to fix it via taxes, regulation, property rights) | Clean split: MKT identifies the disease; POL prescribes the cure. Boundary principle P5: mechanism vs. intervention. |
| Tax incidence | MKT provides the supply-demand framework for analyzing who bears the tax burden | DEF-POL002 (tax incidence as a policy analysis tool) | POL owns the analysis. MKT provides the equilibrium and elasticity frameworks that POL imports. |
| Price control | DEF-MKT003 (how price controls create shortages/surpluses) | POL uses price controls as policy instruments | MKT owns the market mechanism (what happens when equilibrium is disrupted). POL decides whether to impose the control. |
| Public good | DEF-MKT007 (market failure diagnosis -- why the market undersupplies) | PRIM-POL001 imports this to justify government provision | Same split as externality: MKT diagnoses; POL intervenes. |

## 6. Real-World Hooks

| ID | Concept | Everyday Application |
|----|---------|---------------------|
| PRIM-MKT001 | Demand reasoning | When a celebrity endorses a product, demand shifts right -- why your favorite brand costs more after going viral |
| PRIM-MKT002 | Supply reasoning | A drought destroys coffee crops, supply shifts left, coffee prices rise at your local cafe |
| PRIM-MKT003 | Equilibrium reasoning | The semiconductor shortage of 2021: supply shifted left, demand shifted right, electronics prices soared |
| PRIM-MKT004 | Elasticity reasoning | OPEC raises oil prices and earns more revenue because gas demand is inelastic -- people still need to drive |
| PRIM-MKT005 | Market structure reasoning | Why your cell phone plan is so expensive: the wireless industry is an oligopoly with high barriers to entry |
| DEF-MKT001 | Demand curve | A concert that sells out instantly signals the ticket price was below where the demand curve crosses the capacity |
| DEF-MKT002 | Supply curve | Housing in San Francisco: nearly vertical supply curve means increased demand raises prices, not construction |
| DEF-MKT003 | Price ceiling and floor | Rent control (price ceiling) creates housing shortages; minimum wage (price floor) may create unemployment |
| DEF-MKT004 | Consumer and producer surplus | Buying a used textbook for $20 when you would have paid $50 -- you captured $30 of consumer surplus |
| DEF-MKT005 | Deadweight loss | A sugar tax blocks some trades where the buyer values the drink more than it costs to produce -- that value vanishes |
| DEF-MKT006 | Externality | Factory pollution: the product is priced too low because the price does not include health costs to neighbors |
| DEF-MKT007 | Public good | Lighthouses, national defense, clean air -- goods the market will not provide because everyone free-rides |

## 7. Intra-Domain Dependency Graph

```
PRIM-MKT001 (Demand reasoning)     PRIM-MKT002 (Supply reasoning)
     |                                    |
     +---> DEF-MKT001 (Demand curve)      +---> DEF-MKT002 (Supply curve)
     |                                    |
     +---+---+----------------------------+
         |   |
         v   v
     PRIM-MKT003 (Equilibrium reasoning)     PRIM-MKT004 (Elasticity reasoning)
         |                                        [depends on MKT001, MKT002]
         +---> PRIM-MKT005 (Market structure reasoning)
         |         [also depends on CHO: PRIM-CHO003]
         |
         +---> DEF-MKT003 (Price ceiling and floor)
         |
         +---> DEF-MKT004 (Consumer and producer surplus)
         |         [also depends on DEF-MKT001, DEF-MKT002]
         |         |
         |         +---> DEF-MKT005 (Deadweight loss)
         |                    |
         |                    +---> DEF-MKT006 (Externality)
         |                              |
         |                              +---> DEF-MKT007 (Public good)
         |                                       [also depends on CHO: PRIM-CHO004]
```

**Acyclicity verification**: All arrows point from items with lower depth to items with higher depth. PRIM-MKT001 and PRIM-MKT002 are the two roots (both depend only on CHO imports). No item depends on an item of equal or greater depth through a cycle. The graph is a DAG.

**Core-only subgraph**: Removing DEF-MKT007 (E) leaves all Core items with satisfied dependencies. No Core item depends on DEF-MKT007.

## 8. Cross-Domain Interface

### Exports

| ID | Concept | Imported by |
|----|---------|-------------|
| PRIM-MKT001 | Demand reasoning | MAC, POL |
| PRIM-MKT002 | Supply reasoning | MAC, POL |
| PRIM-MKT003 | Equilibrium reasoning | MAC, POL |
| PRIM-MKT004 | Elasticity reasoning | POL |
| PRIM-MKT005 | Market structure reasoning | POL |
| DEF-MKT001 | Demand curve | MAC |
| DEF-MKT002 | Supply curve | MAC |
| DEF-MKT003 | Price ceiling and floor | POL |
| DEF-MKT004 | Consumer and producer surplus | POL |
| DEF-MKT005 | Deadweight loss | POL |
| DEF-MKT006 | Externality | POL |
| DEF-MKT007 | Public good | POL |

### Imports

| DEP ID | Imported Item | From Domain | Used by |
|--------|---------------|-------------|---------|
| DEP-MKT001 | PRIM-CHO001 (Scarcity reasoning) | CHO | Foundation for why markets exist |
| DEP-MKT002 | PRIM-CHO002 (Opportunity cost reasoning) | CHO | Underlies supply curve (cost of production) |
| DEP-MKT003 | PRIM-CHO003 (Marginal analysis) | CHO | Demand reflects diminishing MB; supply reflects rising MC |
| DEP-MKT004 | PRIM-CHO004 (Incentive reasoning) | CHO | Demand and supply respond to price incentives |
| DEP-MKT005 | DEF-CHO002 (Diminishing marginal returns) | CHO | Explains upward slope of supply curve |
| DEP-MKT006 | AX-CHO001 (Rational self-interest) | CHO | Behavioral foundation for supply and demand |

## 9. Difficulty Tiers

| ID | Concept | Tier | Justification |
|----|---------|------|---------------|
| PRIM-MKT001 | Demand reasoning | C | Foundational: one of the two blades of Marshall's scissors |
| PRIM-MKT002 | Supply reasoning | C | Foundational: the other blade of the scissors |
| PRIM-MKT003 | Equilibrium reasoning | C | Core analytical tool: every market question is an equilibrium question |
| PRIM-MKT004 | Elasticity reasoning | C | Core threshold concept: transforms demand/supply from qualitative to quantitative; essential for policy analysis |
| PRIM-MKT005 | Market structure reasoning | C | Core classification: explains why different industries behave differently |
| DEF-MKT001 | Demand curve | C | Core visualization: the graphical foundation of demand analysis |
| DEF-MKT002 | Supply curve | C | Core visualization: the graphical foundation of supply analysis |
| DEF-MKT003 | Price ceiling and floor | C | Core policy application: the simplest government intervention in markets |
| DEF-MKT004 | Consumer and producer surplus | C | Core welfare tool: the standard measure of market efficiency |
| DEF-MKT005 | Deadweight loss | C | Core efficiency concept: the cost of market distortions |
| DEF-MKT006 | Externality | C | Core market failure: the foundational case for government intervention |
| DEF-MKT007 | Public good | E | Enrichment: important but can be omitted without breaking Core dependency chains; no Core item depends on it |

**Tier constraint verification**: The sole Enrichment item is DEF-MKT007 (Public good). No Core item depends on DEF-MKT007. Removing it leaves all 11 Core items with fully satisfied dependency chains.

## 10. Self-Audit Checklist

- [x] Every PRIM has: reasoning move formulation ("Given X, do Y to determine Z"), description, semi-formal statement, depends, ownership, source, referenced-by, tier, real-world hook
- [x] Every DEF depends only on previously listed PRIM/DEF (verified via intra-domain dependency graph)
- [x] Every cross-domain reference uses full `{Type}-{Code}{Number}` format
- [x] Every import is listed in CHO's exports (PRIM-CHO001, PRIM-CHO002, PRIM-CHO003, PRIM-CHO004, DEF-CHO002, AX-CHO001 -- all present in DOMAIN-CHO.md Section 9)
- [x] Dissolution argument is present and non-trivial (3+ sentences explaining why MKT cannot merge into CHO, MAC, or POL)
- [x] Real-world hooks cover everyday non-major contexts (avocados, coffee, concerts, cell phone plans, rent control, used textbooks, lighthouses)
- [x] Intra-domain dependency graph is acyclic (verified: two roots PRIM-MKT001 and PRIM-MKT002; all edges point downward)
- [x] Tier annotations (C/E) are present on all 12 items
- [x] No PRIM/DEF duplicates an entry in another domain (checked against Primitive Registry)
- [x] Reasoning moves are genuinely "Given X, do Y" cognitive operations (not mere topic labels)
