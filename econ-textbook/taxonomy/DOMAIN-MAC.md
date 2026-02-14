# DOMAIN-MAC v0.1

## 0. Sources & Assumptions

- SRC-MAC001: Solow, "A Contribution to the Theory of Economic Growth," *Quarterly Journal of Economics*, 1956 (foundation of growth accounting)
- SRC-MAC002: Keynes, *The General Theory of Employment, Interest, and Money*, 1936 (foundation of aggregate demand analysis)
- SRC-MAC003: Phillips, "The Relation Between Unemployment and the Rate of Change of Money Wage Rates," *Economica*, 1958 (inflation-unemployment tradeoff)
- SRC-GLB001: OpenStax, *Principles of Economics*, 3rd ed., 2023, Ch. 19--27
- SRC-GLB002: Mankiw, *Principles of Economics*, 9th ed., 2021, Ch. 23--28, 33--36
- SRC-GLB007: Samuelson & Nordhaus, *Economics*, 19th ed., 2010, Ch. 20--27
- ASM-MAC001: Macroeconomic measurement is presented through intuitive reasoning about aggregates, not through national income accounting identities in full formal detail. Justification: non-majors need to reason about what GDP, unemployment, and inflation mean and why they matter, not perform accounting exercises (ASM-GLB002).
- ASM-MAC002: Business cycle analysis is presented qualitatively (expansion, peak, contraction, trough) without formal mathematical models. Justification: non-majors need the reasoning framework for interpreting economic news, not for forecasting.

## 1. Domain Intent

- **Governing question**: How does the economy behave in aggregate?
- **Scope**: Measuring and reasoning about economy-wide outcomes: total output (GDP), the labor market (unemployment), the general price level (inflation), the business cycle, aggregate demand and aggregate supply, and international trade flows. MAC provides the aggregate layer: what happens when millions of individual market decisions add up to national-level outcomes.
- **Non-goals**: How individual agents decide (CHO). How individual markets determine prices for specific goods (MKT). How the banking system creates money or how the central bank operates (MON). What specific fiscal or monetary policies governments should adopt (POL).
- **Dissolution argument**: Macroeconomics answers questions about the economy AS A WHOLE that cannot be answered by analyzing individual markets. GDP measures total output, not the output of any single industry. The unemployment rate measures the fraction of the labor force without work, not the labor conditions in any single firm. Inflation measures the rate of change of the GENERAL price level, not the price of any single good. These aggregate phenomena exhibit emergent properties -- the paradox of thrift (individual saving is prudent, but if everyone saves simultaneously, aggregate demand falls and everyone is worse off) cannot be captured by micro-level market analysis. Merging MAC into MKT would lose these emergent aggregate properties. You can understand the wheat market perfectly without knowing the GDP growth rate; conversely, you can measure GDP without analyzing any single market in detail.
- **Threshold schema mapping**: Individual --> Aggregate. The foundational conceptual shift in MAC is recognizing that aggregate outcomes can differ qualitatively from individual outcomes. What is rational for one person (saving more) can be collectively harmful (paradox of thrift). What raises one price (supply reduction in one market) may not raise the general price level (inflation requires economy-wide forces).

## 2. Prerequisites

MAC depends on CHO and MKT and imports the following:

| DEP ID | Imported Item | Reason |
|--------|---------------|--------|
| DEP-MAC001 | PRIM-CHO001 (Scarcity reasoning) | National economies face scarcity: finite labor, capital, natural resources limit total output |
| DEP-MAC002 | PRIM-CHO002 (Opportunity cost reasoning) | Macroeconomic tradeoffs (guns vs. butter, consumption vs. investment) are opportunity cost questions at the national level |
| DEP-MAC003 | DEF-CHO001 (PPF) | The PPF is the visual representation of the economy's productive capacity; economic growth shifts the PPF outward |
| DEP-MAC004 | DEF-CHO003 (Comparative advantage) | International trade patterns are explained by comparative advantage at the country level |
| DEP-MAC005 | PRIM-MKT001 (Demand reasoning) | Aggregate demand is built from the concept of demand applied to the entire economy |
| DEP-MAC006 | PRIM-MKT002 (Supply reasoning) | Aggregate supply is built from the concept of supply applied to the entire economy |
| DEP-MAC007 | DEF-MKT001 (Demand curve) | The AD curve is a macro-level adaptation of the demand curve |
| DEP-MAC008 | DEF-MKT002 (Supply curve) | The AS curve is a macro-level adaptation of the supply curve |

MAC does NOT depend on MON or POL:
- **MAC does not depend on MON**: GDP, unemployment, inflation, and business cycles can be defined and measured without reference to the banking system, money creation, or central bank operations. These are aggregate outcomes observable in any economy, even a hypothetical barter economy.
- **MAC does not depend on POL**: Macroeconomic phenomena exist independently of government intervention. Business cycles occurred before fiscal or monetary policy existed. MAC measures the economy; POL attempts to manage it.

## 3. Primitives

- PRIM-MAC001: **GDP reasoning**
  - Reasoning move: Given data about an economy's output over a time period, determine what is and is not counted in GDP to assess the economy's total production, and distinguish between GDP growth (more output) and mere price increases (inflation).
  - Description: The cognitive operation of measuring the total value of all final goods and services produced within a country in a given time period. GDP is the single most important macroeconomic statistic. GDP reasoning involves three key skills: (1) knowing what counts (final goods, not intermediate goods; market transactions, not household production or illegal activity); (2) distinguishing nominal GDP (measured in current prices) from real GDP (adjusted for inflation); (3) interpreting GDP growth as a measure of economic health. GDP can be measured three equivalent ways: the expenditure approach (C + I + G + NX), the income approach (sum of all incomes earned), and the production approach (sum of value added). For non-majors, the expenditure approach is primary.
  - Semi-formal: GDP = C + I + G + NX, where C = consumer spending, I = business investment, G = government purchases, NX = net exports (exports - imports). Nominal GDP = sum of (P_i * Q_i) at current prices. Real GDP = sum of (P_base * Q_i) at base-year prices. GDP growth rate = (GDP_t - GDP_{t-1}) / GDP_{t-1} * 100%. GDP does not count: intermediate goods (to avoid double counting), used goods (already counted when new), financial transactions (not production), or household production.
  - Depends: PRIM-CHO001 (scarcity reasoning -- GDP measures the economy's total output from scarce resources)
  - Ownership: MAC
  - Source: SRC-GLB001 (OpenStax Ch. 19), SRC-GLB002 (Mankiw Ch. 23), SRC-GLB007 (Samuelson Ch. 21)
  - Referenced by: POL
  - Tier: C
  - Real-world hook: When the news says "the economy grew 2.5% last quarter," they mean real GDP increased by 2.5%. When they say "the economy is in recession," they mean real GDP declined for two consecutive quarters. GDP is the thermometer of the economy -- it does not tell you everything, but it tells you the most important thing: are we producing more or less than before?

- PRIM-MAC002: **Unemployment reasoning**
  - Reasoning move: Given labor market data, calculate the unemployment rate, distinguish between types of unemployment (frictional, structural, cyclical), and assess whether unemployment is above or below its natural rate.
  - Description: The cognitive operation of interpreting unemployment data and understanding its causes. The unemployment rate is the percentage of the labor force that is jobless and actively seeking work. Not all unemployment is the same: frictional unemployment is short-term, caused by job transitions (normal and healthy). Structural unemployment is long-term, caused by mismatches between workers' skills and available jobs (more concerning). Cyclical unemployment is caused by economic downturns (the target of macroeconomic policy). The natural rate of unemployment is the rate when cyclical unemployment is zero -- it includes only frictional and structural components. When actual unemployment exceeds the natural rate, the economy has slack; when below, the economy may be overheating.
  - Semi-formal: Labor force = employed + unemployed (seeking work). Unemployment rate = (unemployed / labor force) * 100%. Not in labor force: retired, students, discouraged workers, caregivers. Natural rate of unemployment U_n = frictional + structural. Cyclical unemployment = actual rate - U_n. If cyclical > 0, economy is below potential. If cyclical < 0, economy is above potential (possible overheating).
  - Depends: PRIM-CHO001 (scarcity reasoning -- labor is a scarce resource; unemployment represents underutilization of that resource)
  - Ownership: MAC
  - Source: SRC-GLB001 (OpenStax Ch. 21), SRC-GLB002 (Mankiw Ch. 28)
  - Referenced by: POL
  - Tier: C
  - Real-world hook: When you hear "unemployment fell to 3.5%," that sounds good. But the number hides detail: are the new jobs full-time or part-time? Are previously discouraged workers re-entering the labor force? Is unemployment low because the economy is booming (cyclical drop) or because workers in declining industries have given up looking (they are no longer counted)? Unemployment reasoning cuts through the headline number.

- PRIM-MAC003: **Inflation reasoning**
  - Reasoning move: Given price-level data over time, calculate the inflation rate, distinguish between causes of inflation (demand-pull vs. cost-push), and assess the economic consequences of inflation for different groups (savers, borrowers, wage earners).
  - Description: The cognitive operation of understanding why the general price level rises and who wins and loses. Inflation is a sustained increase in the general price level, NOT a one-time price jump in a single market. The Consumer Price Index (CPI) measures inflation by tracking the price of a basket of goods. Demand-pull inflation occurs when aggregate demand exceeds aggregate supply (too much money chasing too few goods). Cost-push inflation occurs when production costs rise economy-wide (oil shocks, supply chain disruptions). Inflation is not neutral: it redistributes wealth from lenders to borrowers (who repay in cheaper dollars), from savers to spenders, and from people on fixed incomes to those with negotiating power. Unexpected inflation is worse than expected inflation because it prevents people from adjusting.
  - Semi-formal: Inflation rate = (CPI_t - CPI_{t-1}) / CPI_{t-1} * 100%. CPI = weighted average of prices of a fixed basket of goods. Demand-pull: AD shifts right faster than AS. Cost-push: AS shifts left (higher production costs). Real interest rate = nominal interest rate - inflation rate (Fisher equation). Inflation tax: inflation erodes the purchasing power of cash holdings.
  - Depends: PRIM-MAC001 (GDP reasoning -- inflation is distinguished from real growth by separating price changes from quantity changes)
  - Ownership: MAC
  - Source: SRC-GLB001 (OpenStax Ch. 22), SRC-GLB002 (Mankiw Ch. 24), SRC-MAC003 (Phillips 1958)
  - Referenced by: MON, POL
  - Tier: C
  - Real-world hook: In 2022, US inflation hit 9.1% -- the highest in 40 years. Your rent, groceries, and gas all cost more. But if your wages rose only 5%, your real purchasing power fell by 4%. Meanwhile, if you had a fixed-rate mortgage, inflation was actually helping you: you were repaying the bank with dollars worth less than when you borrowed them. Inflation reasoning tells you who wins and who loses.

- PRIM-MAC004: **Price level reasoning**
  - Reasoning move: Given economic data, distinguish between changes in the price of individual goods (relative price changes) and changes in the overall price level, and connect the aggregate price level to macroeconomic forces rather than individual market forces.
  - Description: The cognitive operation of separating micro-level price changes from macro-level price-level changes. When the price of lettuce rises because of a drought, that is a relative price change driven by supply and demand in the lettuce market. When ALL prices rise simultaneously, that is a change in the general price level driven by macroeconomic forces (excess money supply, aggregate demand exceeding aggregate supply). Students routinely conflate these: they think inflation is caused by "greedy companies raising prices," confusing individual pricing decisions with economy-wide phenomena. Price level reasoning is the analytical move that separates the two: individual prices are determined by market supply and demand; the general price level is determined by the interaction of aggregate demand, aggregate supply, and the money supply.
  - Semi-formal: Price level P = aggregate price index (CPI, GDP deflator). Change in P = inflation. A change in the relative price of good i: P_i increases while other prices may not. A change in the price level: most prices increase simultaneously. Relative price change: driven by supply/demand in market i. Price level change: driven by AD/AS shifts or money supply changes.
  - Depends: PRIM-MAC003 (inflation reasoning -- the price level is the aggregate measure whose rate of change is inflation), PRIM-MKT003 (equilibrium reasoning -- individual prices are determined by market equilibrium; the price level is determined by aggregate equilibrium)
  - Ownership: MAC
  - Source: SRC-GLB001 (OpenStax Ch. 22), SRC-GLB002 (Mankiw Ch. 24)
  - Referenced by: MON
  - Tier: C
  - Real-world hook: In 2022, people blamed inflation on "corporations being greedy." But corporate greed is not new -- companies always try to charge the most they can. What changed was macroeconomic conditions: massive fiscal stimulus increased aggregate demand while supply chains were still disrupted. Price level reasoning separates the macro-level cause (AD outpacing AS) from the micro-level symptom (higher prices at specific stores).

- PRIM-MAC005: **Business cycle reasoning**
  - Reasoning move: Given macroeconomic indicators (GDP growth, unemployment, inflation), identify the current phase of the business cycle (expansion, peak, contraction, trough) and predict the likely direction of economic change.
  - Description: The cognitive operation of recognizing that economies do not grow in a straight line but fluctuate in recurring patterns. The business cycle has four phases: expansion (GDP rising, unemployment falling, confidence growing), peak (the high point before the downturn), contraction/recession (GDP falling, unemployment rising, spending declining), and trough (the low point before recovery). Business cycle reasoning combines GDP, unemployment, and inflation data into a holistic assessment of where the economy stands and where it is headed. Leading indicators (stock market, building permits, consumer confidence) signal turns before they happen. Lagging indicators (unemployment rate) confirm turns after they occur.
  - Semi-formal: Business cycle phases: expansion (real GDP growth > 0, unemployment falling), peak (growth rate reaches maximum, begins to decline), contraction (real GDP growth < 0 for 2+ quarters = recession), trough (growth rate reaches minimum, begins to recover). Recession = 2 consecutive quarters of negative real GDP growth (common definition). Each phase has characteristic combinations of GDP, unemployment, and inflation behavior.
  - Depends: PRIM-MAC001 (GDP reasoning -- the cycle is defined by GDP fluctuations), PRIM-MAC002 (unemployment reasoning -- unemployment is a key cyclical indicator), PRIM-MAC003 (inflation reasoning -- inflation behavior differs across cycle phases)
  - Ownership: MAC
  - Source: SRC-GLB001 (OpenStax Ch. 19, 24), SRC-GLB002 (Mankiw Ch. 33)
  - Referenced by: POL
  - Tier: C
  - Real-world hook: In early 2020, the US economy went from expansion to the sharpest contraction in modern history within weeks (COVID-19). In 2021, it recovered rapidly (trough to expansion). By late 2022, the question was: "Are we heading for another recession?" Business cycle reasoning helps you interpret the competing economic headlines and assess where we actually stand.

## 4. Definitions

- DEF-MAC001: **Nominal vs. real values**
  - Reasoning move: Given an economic quantity measured in current dollars (nominal), adjust it for inflation to obtain the real value, which measures actual purchasing power or physical output.
  - Description: Nominal values are measured in current-period prices. Real values are adjusted for inflation (measured in base-period prices). This distinction matters because a $50,000 salary in 2024 dollars has less purchasing power than the same nominal salary in 2000 dollars. GDP, wages, interest rates, and other economic variables all require this adjustment. The key formula: real value = nominal value / price index * 100. Without this adjustment, you cannot tell whether an increase in GDP reflects more stuff being produced (real growth) or just higher prices (inflation).
  - Semi-formal: Real value = nominal value * (P_base / P_current). Equivalently: real value = nominal value / (CPI_current / 100) when CPI base = 100. Real GDP growth = nominal GDP growth - inflation rate (approximately). Real wage = nominal wage / price level. Real interest rate = nominal interest rate - inflation rate.
  - Depends: PRIM-MAC001 (GDP reasoning -- nominal vs. real is essential for interpreting GDP data), PRIM-MAC003 (inflation reasoning -- inflation is the wedge between nominal and real values)
  - Ownership: MAC
  - Source: SRC-GLB001 (OpenStax Ch. 19, 22), SRC-GLB002 (Mankiw Ch. 24)
  - Referenced by: MON
  - Tier: C
  - Real-world hook: Your grandparents say "I bought my house for $20,000 in 1970." That sounds impossibly cheap, but $20,000 in 1970 had the purchasing power of about $160,000 today (adjusting for inflation). Nominal vs. real reasoning prevents misleading comparisons across time.

- DEF-MAC002: **Aggregate demand**
  - Reasoning move: Given factors that affect total spending in the economy (consumer confidence, government spending, net exports, interest rates), determine the direction of aggregate demand shift and predict the effect on GDP and the price level.
  - Description: Aggregate demand (AD) is the total demand for all final goods and services in the economy at each price level. The AD curve is downward-sloping (higher price level reduces total spending) for three reasons: the wealth effect (higher prices reduce purchasing power of savings), the interest-rate effect (higher prices increase demand for money, raising interest rates, reducing investment), and the net-export effect (higher domestic prices make exports less competitive). AD shifts when any component of spending (C, I, G, NX) changes for reasons other than the price level. AD is the macro-level application of demand reasoning (PRIM-MKT001), but it operates on the entire economy, not a single market.
  - Semi-formal: AD curve: P_level --> GDP_demanded. Downward-sloping: higher P_level --> lower GDP_demanded. AD = C + I + G + NX (at each price level). AD shifts right when: consumer confidence rises, government spending increases, taxes decrease, investment increases, net exports increase. AD shifts left for the opposite changes.
  - Depends: PRIM-MAC001 (GDP reasoning -- AD determines total output), PRIM-MKT001 (demand reasoning -- AD is the aggregate version of demand), DEF-MKT001 (demand curve -- AD curve is a macro adaptation)
  - Ownership: MAC
  - Source: SRC-GLB001 (OpenStax Ch. 24), SRC-GLB002 (Mankiw Ch. 33), SRC-MAC002 (Keynes 1936)
  - Referenced by: POL
  - Tier: C
  - Real-world hook: During COVID-19, governments sent stimulus checks to households. This increased consumer spending (C), shifting aggregate demand right. At the same time, supply chains were disrupted (AS shifted left). The combination of more demand hitting less supply produced both economic recovery AND inflation -- a textbook AD-AS analysis.

- DEF-MAC003: **Aggregate supply**
  - Reasoning move: Given factors that affect the economy's total production capacity (input costs, technology, labor force size, regulation), determine the direction of aggregate supply shift and predict the effect on GDP and the price level.
  - Description: Aggregate supply (AS) is the total quantity of goods and services that firms are willing to produce at each price level. The short-run AS (SRAS) curve is upward-sloping: when the price level rises, firms produce more because revenues rise while some input costs (wages, contracts) are temporarily fixed. The long-run AS (LRAS) curve is vertical at potential GDP: in the long run, output is determined by resources and technology, not the price level. AS shifts when input costs, technology, or the quantity/quality of resources changes. Cost-push inflation is an AS-driven phenomenon: higher production costs shift AS left, reducing output and raising the price level simultaneously (stagflation).
  - Semi-formal: SRAS curve: P_level --> GDP_supplied (upward-sloping in short run). LRAS: vertical at Y_potential (determined by resources and technology). SRAS shifts left when: input costs rise, supply chain disruptions occur, regulation increases costs. SRAS shifts right when: technology improves, input costs fall, productivity increases. LRAS shifts right with: capital accumulation, labor force growth, technological progress (economic growth).
  - Depends: PRIM-MAC001 (GDP reasoning -- AS determines total output at each price level), PRIM-MKT002 (supply reasoning -- AS is the aggregate version of supply), DEF-MKT002 (supply curve -- AS curve is a macro adaptation)
  - Ownership: MAC
  - Source: SRC-GLB001 (OpenStax Ch. 24), SRC-GLB002 (Mankiw Ch. 33)
  - Referenced by: POL
  - Tier: C
  - Real-world hook: When oil prices spiked in the 1970s, production costs rose across the entire economy. Aggregate supply shifted left: the economy produced less output at higher prices. This was stagflation -- inflation and recession simultaneously. AS reasoning explains why it happened and why standard demand-side stimulus would not fix it (more demand would just cause more inflation without increasing output).

- DEF-MAC004: **Multiplier effect**
  - Reasoning move: Given an initial change in spending (e.g., government stimulus), trace the chain of re-spending to determine the total effect on GDP, recognizing that the final impact is larger than the initial injection.
  - Description: The multiplier effect is the amplification of an initial spending change through successive rounds of re-spending. When the government spends $1 billion building a bridge, the construction workers receive income and spend (say) 80% of it. The businesses they buy from receive that income and spend 80% of it, and so on. Each round is smaller, but the total impact converges to a multiple of the original spending: with an 80% marginal propensity to consume (MPC), the multiplier is 1/(1-MPC) = 1/0.2 = 5. So the $1 billion in government spending generates $5 billion in total GDP. The multiplier works in reverse too: a cut in spending contracts GDP by a multiple. The multiplier explains why small changes in investment or government spending can cause large swings in GDP.
  - Semi-formal: Multiplier = 1 / (1 - MPC), where MPC = marginal propensity to consume (fraction of additional income that is spent). If MPC = 0.8, multiplier = 5. Total GDP change = multiplier * initial spending change. Spending multiplier: delta-GDP = [1/(1-MPC)] * delta-G. Tax multiplier: delta-GDP = [-MPC/(1-MPC)] * delta-T (smaller because part of the tax cut is saved).
  - Depends: DEF-MAC002 (aggregate demand -- the multiplier operates through successive shifts in AD), PRIM-CHO003 (marginal analysis -- MPC is a marginal concept)
  - Ownership: MAC
  - Source: SRC-GLB001 (OpenStax Ch. 25), SRC-GLB002 (Mankiw Ch. 34), SRC-MAC002 (Keynes 1936)
  - Referenced by: POL
  - Tier: E
  - Real-world hook: In 2009, the US government passed an $800 billion stimulus package. Economists debated whether the multiplier was 1.5 (total effect = $1.2 trillion) or 0.5 (total effect = only $400 billion, as government spending crowded out private spending). The multiplier is not a fixed number -- it depends on economic conditions. But the concept explains why governments try to "jump-start" the economy with spending.

- DEF-MAC005: **Trade balance**
  - Reasoning move: Given data on a country's exports and imports, calculate the trade balance and determine whether the country has a trade surplus (exports > imports) or deficit (imports > exports), and connect the trade balance to exchange rates, savings, and investment.
  - Description: The trade balance is the difference between a country's exports and imports. A trade surplus (positive NX) means the country sells more to the rest of the world than it buys; a trade deficit (negative NX) means the opposite. The trade balance is connected to the savings-investment balance: a trade deficit corresponds to the country borrowing from abroad (importing more than it produces, financing the difference with foreign capital). A trade deficit is NOT inherently bad -- it may reflect strong domestic investment opportunities that attract foreign capital. Trade balance reasoning corrects the common misconception that trade deficits are "losing" and surpluses are "winning."
  - Semi-formal: Trade balance NX = exports - imports. NX > 0: trade surplus. NX < 0: trade deficit. National savings identity: S - I = NX. If S < I (the country invests more than it saves domestically), NX < 0 (capital inflow finances the difference). Trade deficit = capital account surplus.
  - Depends: PRIM-MAC001 (GDP reasoning -- NX is a component of GDP), DEF-CHO003 (comparative advantage -- trade patterns are driven by comparative advantage)
  - Ownership: MAC
  - Source: SRC-GLB001 (OpenStax Ch. 23), SRC-GLB002 (Mankiw Ch. 31)
  - Referenced by: POL
  - Tier: E
  - Real-world hook: The US has run a trade deficit for decades. Politicians call it a crisis. Economists are more nuanced: the deficit means foreigners are investing heavily in the US (buying Treasury bonds, building factories). A trade deficit is the flip side of a capital surplus. Trade balance reasoning helps you evaluate whether "we're losing at trade" is accurate or misleading.

## 5. Contested Concepts

The primary contested boundary for MAC is with MON and MKT.

| Concept | MAC Version (Owner) | Other Domain Version | Resolution |
|---------|---------------------|----------------------|------------|
| Price level | PRIM-MAC004 (aggregate price index) | MON connects money supply to price level (quantity theory) | MAC owns the measurement and meaning of the price level. MON explains one mechanism (money supply) that influences it. Boundary principle P2: aggregate measurement is MAC; monetary mechanism is MON. |
| Aggregate demand | DEF-MAC002 (total spending at each price level) | MON influences AD through interest rate channel | MAC owns AD as a concept. MON provides one of the channels through which AD is influenced. |
| Individual market price changes | MKT owns individual market equilibrium | MAC distinguishes individual price changes from general price level changes (PRIM-MAC004) | Clean split: MKT analyzes one market at a time. MAC analyzes the economy-wide price level. Boundary principle P2: individual market is MKT; economy-wide aggregate is MAC. |

## 6. Real-World Hooks

| ID | Concept | Everyday Application |
|----|---------|---------------------|
| PRIM-MAC001 | GDP reasoning | "The economy grew 2.5% last quarter" -- GDP reasoning tells you this means more goods and services were produced, adjusted for inflation |
| PRIM-MAC002 | Unemployment reasoning | The headline "unemployment fell to 3.5%" hides crucial detail -- are new jobs full-time? Are discouraged workers re-entering? |
| PRIM-MAC003 | Inflation reasoning | 9.1% inflation in 2022: your wages rose 5%, so your real purchasing power fell 4%. Borrowers benefited; savers lost. |
| PRIM-MAC004 | Price level reasoning | "Corporate greed causes inflation" confuses micro pricing decisions with macro-level aggregate demand/supply forces |
| PRIM-MAC005 | Business cycle reasoning | COVID-19 recession: expansion to contraction in weeks, recovery within a year -- textbook business cycle |
| DEF-MAC001 | Nominal vs. real | "Houses cost $20,000 in 1970" -- adjusted for inflation, that is about $160,000 in today's dollars |
| DEF-MAC002 | Aggregate demand | COVID stimulus checks shifted AD right while supply chains were disrupted -- producing both recovery AND inflation |
| DEF-MAC003 | Aggregate supply | 1970s oil shocks shifted AS left: stagflation (inflation + recession simultaneously) |
| DEF-MAC004 | Multiplier effect | The 2009 stimulus: $800 billion in spending, but how much total GDP impact? Depends on the multiplier |
| DEF-MAC005 | Trade balance | The US trade deficit is not "losing" -- it is the flip side of massive foreign investment in America |

## 7. Intra-Domain Dependency Graph

```
PRIM-MAC001 (GDP reasoning)
     |
     +---> PRIM-MAC003 (Inflation reasoning)
     |          |
     |          +---> PRIM-MAC004 (Price level reasoning)
     |                    [also depends on PRIM-MKT003 from MKT]
     |
     +---> DEF-MAC001 (Nominal vs. real) [also depends on PRIM-MAC003]
     |
     +---> DEF-MAC002 (Aggregate demand)
     |          [also depends on PRIM-MKT001, DEF-MKT001]
     |          |
     |          +---> DEF-MAC004 (Multiplier effect) [E]
     |
     +---> DEF-MAC003 (Aggregate supply)
     |          [also depends on PRIM-MKT002, DEF-MKT002]
     |
     +---> DEF-MAC005 (Trade balance) [E]
     |          [also depends on DEF-CHO003]

PRIM-MAC002 (Unemployment reasoning)
     [depends on PRIM-CHO001]

PRIM-MAC005 (Business cycle reasoning)
     [depends on PRIM-MAC001, PRIM-MAC002, PRIM-MAC003]
```

**Acyclicity verification**: All arrows point from lower-depth items to higher-depth items. PRIM-MAC001 and PRIM-MAC002 are the roots (both depend only on CHO imports). PRIM-MAC005 depends on MAC001, MAC002, MAC003. No cycles. The graph is a DAG.

**Core-only subgraph**: Removing DEF-MAC004 (E) and DEF-MAC005 (E) leaves all Core items with satisfied dependencies. No Core item depends on either Enrichment item.

## 8. Cross-Domain Interface

### Exports

| ID | Concept | Imported by |
|----|---------|-------------|
| PRIM-MAC001 | GDP reasoning | POL |
| PRIM-MAC002 | Unemployment reasoning | POL |
| PRIM-MAC003 | Inflation reasoning | MON, POL |
| PRIM-MAC004 | Price level reasoning | MON |
| PRIM-MAC005 | Business cycle reasoning | POL |
| DEF-MAC001 | Nominal vs. real values | MON |
| DEF-MAC002 | Aggregate demand | POL |
| DEF-MAC003 | Aggregate supply | POL |
| DEF-MAC004 | Multiplier effect | POL |
| DEF-MAC005 | Trade balance | POL |

### Imports

| DEP ID | Imported Item | From Domain | Used by |
|--------|---------------|-------------|---------|
| DEP-MAC001 | PRIM-CHO001 (Scarcity reasoning) | CHO | Foundation for national-level scarcity |
| DEP-MAC002 | PRIM-CHO002 (Opportunity cost reasoning) | CHO | National-level tradeoffs |
| DEP-MAC003 | DEF-CHO001 (PPF) | CHO | Economy's productive capacity |
| DEP-MAC004 | DEF-CHO003 (Comparative advantage) | CHO | International trade patterns |
| DEP-MAC005 | PRIM-MKT001 (Demand reasoning) | MKT | Foundation for aggregate demand |
| DEP-MAC006 | PRIM-MKT002 (Supply reasoning) | MKT | Foundation for aggregate supply |
| DEP-MAC007 | DEF-MKT001 (Demand curve) | MKT | AD curve is macro adaptation |
| DEP-MAC008 | DEF-MKT002 (Supply curve) | MKT | AS curve is macro adaptation |

## 9. Difficulty Tiers

| ID | Concept | Tier | Justification |
|----|---------|------|---------------|
| PRIM-MAC001 | GDP reasoning | C | Foundational: the most important macroeconomic statistic; required for all subsequent MAC reasoning |
| PRIM-MAC002 | Unemployment reasoning | C | Core labor market concept: essential for understanding economic health and policy debates |
| PRIM-MAC003 | Inflation reasoning | C | Core price-level concept: essential for real vs. nominal distinction and understanding monetary policy |
| PRIM-MAC004 | Price level reasoning | C | Core analytical distinction: separates micro price changes from macro inflation; prerequisite for MON imports |
| PRIM-MAC005 | Business cycle reasoning | C | Core synthesis: integrates GDP, unemployment, and inflation into a cyclical framework for interpreting economic news |
| DEF-MAC001 | Nominal vs. real values | C | Core tool: without this distinction, all cross-time economic comparisons are meaningless |
| DEF-MAC002 | Aggregate demand | C | Core macro model: one half of the AD-AS framework that is the central tool of macroeconomic analysis |
| DEF-MAC003 | Aggregate supply | C | Core macro model: the other half of AD-AS; required for understanding stagflation, growth, and policy |
| DEF-MAC004 | Multiplier effect | E | Enrichment: valuable for understanding fiscal policy but requires MPC concept; can be omitted without breaking Core chains |
| DEF-MAC005 | Trade balance | E | Enrichment: important for globalization discussions but not required by any Core downstream item |

**Tier constraint verification**: Two Enrichment items (DEF-MAC004, DEF-MAC005). No Core item depends on either. The 8 Core items form a self-contained, dependency-complete sub-taxonomy.

## 10. Self-Audit Checklist

- [x] Every PRIM has: reasoning move formulation, description, semi-formal statement, depends, ownership, source, referenced-by, tier, real-world hook
- [x] Every DEF depends only on previously listed PRIM/DEF (verified via dependency graph)
- [x] Every cross-domain reference uses full `{Type}-{Code}{Number}` format
- [x] Every import is listed in CHO's and MKT's exports (all DEP items verified)
- [x] Dissolution argument is present and non-trivial (multiple sentences; paradox of thrift example; emergent aggregate properties)
- [x] Real-world hooks cover everyday non-major contexts (news headlines, job market, grocery prices, housing, stimulus, trade debates)
- [x] Intra-domain dependency graph is acyclic (two roots; all edges point downward)
- [x] Tier annotations (C/E) are present on all 10 items
- [x] No PRIM/DEF duplicates an entry in another domain (checked against Primitive Registry)
- [x] Reasoning moves are genuinely "Given X, do Y" cognitive operations
