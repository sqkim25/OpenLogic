# DOMAIN-MON v0.1

## 0. Sources & Assumptions

- SRC-MON001: Mishkin, *The Economics of Money, Banking, and Financial Markets*, 12th ed., 2019, Ch. 1--5 (money functions, banking system, central bank operations)
- SRC-MON002: Friedman, "The Quantity Theory of Money -- A Restatement," in *Studies in the Quantity Theory of Money*, 1956 (money-inflation connection)
- SRC-MON003: Bernanke, "The Federal Reserve and the Financial Crisis," 2013 (accessible account of Fed operations for non-specialists)
- SRC-GLB001: OpenStax, *Principles of Economics*, 3rd ed., 2023, Ch. 27--29
- SRC-GLB002: Mankiw, *Principles of Economics*, 9th ed., 2021, Ch. 29--30
- SRC-GLB007: Samuelson & Nordhaus, *Economics*, 19th ed., 2010, Ch. 25--26
- ASM-MON001: Money and banking are presented at the institutional level: what money does, how banks create money through lending, how the central bank influences the money supply. No formal derivation of money demand functions or IS-LM models. Justification: non-majors need to understand the financial system conceptually to interpret news about the Fed, interest rates, and banking crises, not to solve macroeconomic models (ASM-GLB002).
- ASM-MON002: "The Fed" (Federal Reserve) is used as the canonical central bank example. The reasoning moves generalize to any central bank (ECB, Bank of England, etc.). Justification: US-centric source material; the reasoning transfers.

## 1. Domain Intent

- **Governing question**: How does the financial system function?
- **Scope**: The nature and functions of money, the mechanics of the banking system (fractional reserve banking, money creation through lending), interest rates as the price of borrowing, the money supply, central bank operations, and exchange rates. MON provides the financial plumbing layer: the mechanisms through which money is created, interest rates are determined, and the financial system channels savings into investment.
- **Non-goals**: How individual agents make decisions about spending vs. saving (CHO). How individual markets determine prices for goods (MKT). Economy-wide outcomes like GDP, unemployment, or the business cycle (MAC). What monetary policy the government should adopt (POL -- MON describes the tools; POL describes their deployment).
- **Dissolution argument**: The financial system operates by a distinct set of mechanisms that have no analog in goods markets or individual decision-making. Banks create money through the lending process -- a mechanism that does not exist in the supply-demand framework of MKT or the GDP accounting of MAC. Interest rates are the price of borrowing money over time, determined by the supply and demand for loanable funds and central bank policy, not by the supply and demand for any physical good. You can explain supply-demand for wheat (MKT) without knowing anything about fractional reserve banking. You can measure GDP (MAC) without understanding how the Fed conducts open-market operations. Merging MON into MAC would conflate measurement of aggregate outcomes with the financial mechanisms that influence those outcomes. A country could have all the same GDP and unemployment data while having a radically different banking system.
- **Threshold schema mapping**: Money-as-thing --> Money-as-system. The foundational conceptual shift in MON is recognizing that money is not a physical thing (gold coins) but a system of trust, accounting entries, and institutional mechanisms. Most money exists as electronic entries in bank databases, not as physical currency. Banks do not lend out deposits they already have; they create new money when they make loans. Students who fail to cross this threshold think "the Fed prints money" literally, missing the actual mechanism of money creation through bank lending.

## 2. Prerequisites

MON depends on CHO and imports the following:

| DEP ID | Imported Item | Reason |
|--------|---------------|--------|
| DEP-MON001 | PRIM-CHO001 (Scarcity reasoning) | Financial resources are scarce; the interest rate is the price that allocates scarce loanable funds |
| DEP-MON002 | PRIM-CHO003 (Marginal analysis) | Borrowing and lending decisions involve comparing the marginal benefit of using money now vs. later |
| DEP-MON003 | AX-CHO001 (Rational self-interest) | Banks maximize profit; depositors seek the best return; borrowers seek the lowest rate |

MON does NOT depend on MKT, MAC, or POL:
- **MON does not depend on MKT**: Money, banking, and interest rates are defined as financial system properties. Supply-demand diagrams for individual goods markets are not prerequisites for explaining what money is, how banks create it, or why interest rates exist.
- **MON does not depend on MAC**: GDP, unemployment, and inflation are not required to define the functions of money, the mechanics of fractional reserve banking, or the determination of interest rates. Money existed before anyone measured GDP.
- **MON does not depend on POL**: The financial system operates by its own mechanics. Central bank operations (DEF-MON003) describe HOW the Fed works, not what policy it SHOULD adopt. The descriptive mechanics are MON; the prescriptive policy decisions are POL.

## 3. Primitives

- PRIM-MON001: **Money functions reasoning**
  - Reasoning move: Given a candidate item or system, determine whether it serves as money by checking the three functions of money (medium of exchange, store of value, unit of account), and evaluate how well it performs each function.
  - Description: The cognitive operation of understanding what money IS by what it DOES. Money is not defined by its physical form (it can be coins, paper, electronic entries, or even cigarettes in a prison economy). It is defined by its functions: (1) medium of exchange -- you can use it to buy things (eliminates the need for barter); (2) store of value -- it retains purchasing power over time (though inflation erodes this); (3) unit of account -- prices are quoted in it (provides a common measuring stick). Anything that performs all three functions well IS money. This primitive corrects the common misconception that money is intrinsically valuable -- money is valuable because everyone agrees to accept it, not because of the material it is made of.
  - Semi-formal: Item M is money iff: (1) medium of exchange: agents accept M in exchange for goods/services (reduces transaction costs vs. barter); (2) store of value: holding M preserves purchasing power over some time horizon (M does not rapidly lose value); (3) unit of account: prices of goods/services are quoted in units of M (provides a common denominator for comparison). The better M performs all three functions, the better money it is. Inflation degrades function (2). Hyperinflation destroys all three functions.
  - Depends: PRIM-CHO001 (scarcity reasoning -- money facilitates exchange of scarce resources)
  - Ownership: MON
  - Source: SRC-GLB001 (OpenStax Ch. 27), SRC-GLB002 (Mankiw Ch. 29), SRC-MON001 (Mishkin Ch. 3)
  - Referenced by: MAC
  - Tier: C
  - Real-world hook: Bitcoin enthusiasts claim it is "the future of money." Money functions reasoning evaluates this claim: Bitcoin works as a medium of exchange (some merchants accept it), is a questionable store of value (price swings of 50%+ in a year), and is rarely used as a unit of account (almost nothing is priced in Bitcoin). By the three-functions test, Bitcoin is partial money at best.

- PRIM-MON002: **Banking system reasoning**
  - Reasoning move: Given a simplified bank balance sheet (deposits, reserves, loans), trace how a new deposit leads to money creation through the lending process, and explain how the banking system as a whole creates money that did not previously exist.
  - Description: The cognitive operation of understanding that banks do not merely store money -- they create it. When you deposit $1,000 in a bank, the bank keeps a fraction as reserves (say 10%, or $100) and lends out the rest ($900). That $900 loan becomes a deposit at another bank, which keeps 10% ($90) and lends out $810. This process continues, and the original $1,000 deposit ultimately supports many thousands of dollars in total deposits across the banking system. This is fractional reserve banking: banks hold only a fraction of deposits as reserves and lend the rest. The result is that the banking system as a whole creates money -- the total money supply exceeds the physical currency issued by the central bank. This is the most counterintuitive concept in MON: most money is created not by the government but by private banks making loans.
  - Semi-formal: Bank balance sheet: Assets = reserves (R) + loans (L). Liabilities = deposits (D). Required reserve ratio r: banks must hold R >= r * D. Excess reserves: R - r * D (available for lending). When bank lends excess reserves, the borrower's spending creates a new deposit at another bank, which can lend again. Process continues: total money created from initial deposit D_0 = D_0 * (1/r) in the limit (simple money multiplier).
  - Depends: PRIM-MON001 (money functions reasoning -- must understand what money is before understanding how it is created), AX-CHO001 (rational self-interest -- banks lend to earn profit on the interest rate spread)
  - Ownership: MON
  - Source: SRC-GLB001 (OpenStax Ch. 27), SRC-GLB002 (Mankiw Ch. 29), SRC-MON001 (Mishkin Ch. 14)
  - Referenced by: MAC, POL
  - Tier: C
  - Real-world hook: When people panicked during the 2008 financial crisis and withdrew deposits (a "bank run"), they discovered that banks did not have their money sitting in a vault. It had been lent out. That is fractional reserve banking. It is why bank runs are devastating -- and why deposit insurance (FDIC) exists: to prevent the panic in the first place.

- PRIM-MON003: **Interest rate reasoning**
  - Reasoning move: Given information about the supply and demand for loanable funds (or the central bank's policy), determine the equilibrium interest rate, and predict how changes in saving, investment demand, or central bank actions will shift the interest rate and affect borrowing, spending, and investment.
  - Description: The cognitive operation of understanding the interest rate as the price of borrowing money over time. In the loanable funds market, savers supply funds (they are willing to postpone consumption in exchange for interest) and borrowers demand funds (they want to spend now and repay later). The interest rate equilibrates supply and demand, just as any price equilibrates a market. Higher interest rates encourage saving (more supply of loanable funds) but discourage borrowing (less demand). The central bank influences this rate by adjusting the money supply. Interest rate reasoning is the linchpin connecting MON to MAC: the interest rate is the primary channel through which monetary conditions affect the real economy (investment, consumption, housing, business expansion).
  - Semi-formal: In the loanable funds market: supply of LF = savings (S), increases with interest rate r. Demand for LF = investment (I), decreases with r. Equilibrium: r* where S(r*) = I(r*). If the central bank increases money supply, r falls (more funds available). If r falls: investment increases, consumption on credit increases, housing demand increases (lower mortgage rates). Real interest rate = nominal rate - inflation rate.
  - Depends: PRIM-CHO003 (marginal analysis -- borrowers compare the marginal benefit of funds now vs. the marginal cost of interest), PRIM-CHO001 (scarcity reasoning -- loanable funds are scarce)
  - Ownership: MON
  - Source: SRC-GLB001 (OpenStax Ch. 28), SRC-GLB002 (Mankiw Ch. 26, 30), SRC-MON001 (Mishkin Ch. 4)
  - Referenced by: MAC, POL
  - Tier: C
  - Real-world hook: When the Fed raises interest rates, mortgage rates rise. A 30-year mortgage at 3% vs. 7% on a $300,000 home means monthly payments of $1,265 vs. $1,996 -- a $731/month difference. That is why Fed interest rate decisions dominate financial news: they directly affect how much it costs every American to borrow for a home, a car, or a business.

- PRIM-MON004: **Money supply reasoning**
  - Reasoning move: Given the monetary base (currency + bank reserves) and the banking system's reserve ratio, determine the total money supply, and trace how central bank actions (buying/selling bonds, changing reserve requirements) expand or contract the money supply.
  - Description: The cognitive operation of understanding how the total money supply is determined. The money supply is not just the physical currency in circulation -- it includes checking account deposits, which are created through the bank lending process (PRIM-MON002). The central bank controls the monetary base (currency + reserves in the banking system), and the banking system multiplies this base through lending. The central bank expands the money supply by buying government bonds (injecting reserves into the banking system, which then lends them out) or by lowering the reserve requirement (allowing banks to lend more from existing deposits). Understanding the money supply is essential for the quantity theory connection: in the long run, growth in the money supply beyond growth in real output leads to inflation.
  - Semi-formal: Money supply M = monetary base (B) * money multiplier (m). B = currency in circulation + bank reserves. m = 1/r (simple model, where r = reserve ratio). If r = 0.10, m = 10: every $1 of monetary base supports $10 of money supply. Central bank increases B by: buying bonds (open-market purchase), lending to banks (discount window), or lowering reserve requirements (increases m). Quantity equation: M * V = P * Y (money supply * velocity = price level * real output).
  - Depends: PRIM-MON002 (banking system reasoning -- the money multiplier operates through fractional reserve banking), PRIM-MON003 (interest rate reasoning -- the money supply affects the interest rate)
  - Ownership: MON
  - Source: SRC-GLB001 (OpenStax Ch. 27--28), SRC-GLB002 (Mankiw Ch. 29--30), SRC-MON002 (Friedman 1956)
  - Referenced by: MAC, POL
  - Tier: C
  - Real-world hook: During the 2008 crisis and COVID-19, the Fed massively expanded the monetary base through "quantitative easing" (buying bonds). From 2008 to 2022, the Fed's balance sheet grew from $900 billion to $9 trillion. Money supply reasoning explains why many economists predicted the resulting inflation that arrived in 2021-2022: rapid money supply growth eventually shows up in prices.

## 4. Definitions

- DEF-MON001: **Fractional reserve banking**
  - Reasoning move: Given a bank's balance sheet and the required reserve ratio, determine how much the bank can lend, and explain why banks are inherently vulnerable to runs (they hold only a fraction of deposits).
  - Description: Fractional reserve banking is the system in which banks keep only a fraction of their deposits as reserves and lend out the rest. This is the institutional mechanism behind money creation (PRIM-MON002). The reserve ratio determines how much of each deposit must be held in reserve vs. lent out. Lower reserve ratios allow more lending (and more money creation) but increase vulnerability: if too many depositors withdraw simultaneously (a bank run), the bank cannot pay because its assets are tied up in loans. Deposit insurance (FDIC in the US) prevents runs by guaranteeing deposits up to a limit, making the system stable despite its inherent fragility.
  - Semi-formal: Bank balance sheet: Assets = R (reserves) + L (loans). Liabilities = D (deposits). Reserve ratio r = R/D. Required reserves = r * D. Excess reserves = R - r * D. Maximum new lending = excess reserves. If all depositors demand withdrawal simultaneously: bank can pay only R, not D (since R = r * D << D for small r). Bank run: D_withdrawn > R --> bank fails unless it can borrow or sell assets quickly.
  - Depends: PRIM-MON002 (banking system reasoning -- fractional reserve banking is the specific institutional arrangement that enables money creation through lending)
  - Ownership: MON
  - Source: SRC-GLB001 (OpenStax Ch. 27), SRC-GLB002 (Mankiw Ch. 29), SRC-MON001 (Mishkin Ch. 14)
  - Referenced by: POL
  - Tier: C
  - Real-world hook: Silicon Valley Bank collapsed in March 2023 because depositors rushed to withdraw funds after learning the bank had large unrealized losses on its bond portfolio. The bank held only a fraction of deposits as liquid reserves (as all banks do under fractional reserve banking). When withdrawals exceeded reserves, the bank failed within 48 hours. This is exactly the vulnerability that fractional reserve banking creates.

- DEF-MON002: **Money multiplier**
  - Reasoning move: Given the required reserve ratio, calculate the maximum amount of money the banking system can create from a given injection of reserves, and identify the factors that cause the actual multiplier to be smaller than the theoretical maximum.
  - Description: The money multiplier is the ratio of the total money supply to the monetary base. In the simplest model, the multiplier = 1/r, where r is the reserve ratio. If r = 0.10, each dollar of reserves supports up to $10 of deposits. But the actual multiplier is typically smaller than the theoretical maximum because: (1) banks hold excess reserves (more than required, especially during uncertainty); (2) people hold cash (currency outside banks does not get re-deposited and multiplied); (3) borrowers may not re-deposit all loan proceeds. The money multiplier is the key mechanism linking central bank actions (which change the monetary base) to the total money supply (which affects spending and prices).
  - Semi-formal: Simple money multiplier m = 1/r. If r = 0.10, m = 10. Total money supply M = B * m. Adjusted money multiplier: m = (1 + c) / (r + e + c), where c = currency-to-deposit ratio, e = excess reserve ratio, r = required reserve ratio. Higher c or e reduces m. In practice (2020s), the simple multiplier overstates money creation because banks hold large excess reserves.
  - Depends: DEF-MON001 (fractional reserve banking -- the multiplier operates through the fractional reserve lending process), PRIM-MON004 (money supply reasoning -- the multiplier connects the monetary base to the total money supply)
  - Ownership: MON
  - Source: SRC-GLB001 (OpenStax Ch. 27), SRC-GLB002 (Mankiw Ch. 29)
  - Referenced by: POL
  - Tier: C
  - Real-world hook: Before the 2008 crisis, the money multiplier in the US was about 8-9. After 2008, it fell to about 3-4 because banks held massive excess reserves rather than lending. The Fed flooded the banking system with reserves, but banks sat on them -- so the money supply did not grow as much as the textbook multiplier predicted. The gap between theoretical and actual multiplier reveals the importance of bank confidence.

- DEF-MON003: **Central bank operations**
  - Reasoning move: Given the central bank's policy goal (expand or contract the money supply, raise or lower interest rates), identify which tool the central bank uses (open-market operations, discount rate, reserve requirements) and trace how that tool achieves the goal through the banking system.
  - Description: Central bank operations are the specific tools by which the central bank influences the money supply and interest rates. The three main tools are: (1) open-market operations (buying government bonds injects reserves into the banking system, expanding the money supply and lowering interest rates; selling bonds does the reverse); (2) the discount rate (the interest rate the central bank charges banks for emergency loans; a lower rate encourages bank borrowing and lending); (3) reserve requirements (lowering the required reserve ratio increases the money multiplier, expanding the money supply). Open-market operations are by far the most commonly used tool. This definition describes the MECHANICS of how the central bank operates, not the POLICY question of when to use which tool (that is POL).
  - Semi-formal: Open-market purchase: Fed buys bonds --> pays with new reserves --> bank reserves increase --> banks lend more --> money supply increases --> interest rate falls. Open-market sale: reverse. Discount rate: lower rate --> banks borrow more from Fed --> more reserves --> more lending. Reserve requirement: lower r --> higher multiplier m = 1/r --> more money creation from same base. Federal funds rate = overnight interbank lending rate, the Fed's primary target.
  - Depends: PRIM-MON004 (money supply reasoning -- central bank operations change the money supply), PRIM-MON003 (interest rate reasoning -- central bank operations influence the interest rate), DEF-MON002 (money multiplier -- reserve requirement changes work through the multiplier)
  - Ownership: MON
  - Source: SRC-GLB001 (OpenStax Ch. 28), SRC-GLB002 (Mankiw Ch. 30), SRC-MON003 (Bernanke 2013)
  - Referenced by: POL
  - Tier: C
  - Real-world hook: When the news says "the Fed raised rates by 0.25 percentage points," what actually happened is: the Fed conducted open-market sales (sold Treasury bonds), pulling reserves out of the banking system. With fewer reserves, banks raised the interest rate they charge each other for overnight loans (federal funds rate). That rate ripples through to mortgages, car loans, credit cards, and business borrowing. One Fed decision in Washington changes the cost of money for every American.

- DEF-MON004: **Exchange rate**
  - Reasoning move: Given two countries' currencies and economic conditions, determine the exchange rate (price of one currency in terms of another) and predict how changes in interest rates, inflation, trade flows, or investment patterns will cause the exchange rate to appreciate or depreciate.
  - Description: The exchange rate is the price of one country's currency expressed in terms of another's. It is determined by supply and demand in the foreign exchange market. Demand for a currency increases when foreigners want to buy a country's exports, invest in its assets, or benefit from its higher interest rates. A currency appreciates (strengthens) when demand for it rises. A currency depreciates (weakens) when demand falls. Exchange rate movements affect competitiveness: a stronger currency makes exports more expensive (reducing exports) and imports cheaper (increasing imports). Exchange rate reasoning is the MON-level concept; trade balance effects are MAC (DEF-MAC005).
  - Semi-formal: Exchange rate E = units of foreign currency per unit of domestic currency. E increases = appreciation (domestic currency buys more foreign currency). E decreases = depreciation. Factors that cause appreciation: higher domestic interest rates (attract foreign investment), lower domestic inflation (maintains purchasing power), strong economic growth (attracts investment), trade surplus. Purchasing power parity (long run): E adjusts so that the same basket of goods costs the same in both countries when converted.
  - Depends: PRIM-MON003 (interest rate reasoning -- interest rate differentials drive capital flows that affect exchange rates), PRIM-MON001 (money functions reasoning -- exchange rates reflect the relative value of two moneys as stores of value and media of exchange)
  - Ownership: MON
  - Source: SRC-GLB001 (OpenStax Ch. 29), SRC-GLB002 (Mankiw Ch. 31)
  - Referenced by: MAC, POL
  - Tier: E
  - Real-world hook: When the Fed raises interest rates higher than the European Central Bank, global investors move money from euros to dollars (higher return in the US). This increased demand for dollars causes the dollar to appreciate against the euro. A stronger dollar makes your European vacation cheaper (your dollars buy more euros) but makes American exports more expensive for European buyers. Exchange rate reasoning connects domestic monetary policy to global economic effects.

## 5. Contested Concepts

The primary contested boundary for MON is with MAC and POL.

| Concept | MON Version (Owner) | Other Domain Version | Resolution |
|---------|---------------------|----------------------|------------|
| Interest rate | PRIM-MON003 (the price of borrowing; determined by loanable funds and central bank policy) | MAC uses interest rates as a channel through which monetary conditions affect AD | MON owns the concept and mechanism. MAC imports PRIM-MON003 when tracing how interest rate changes affect aggregate demand. Boundary principle P3: financial system mechanics are MON. |
| Money supply | PRIM-MON004 (how the money supply is determined through base x multiplier) | MAC connects money supply growth to inflation | MON owns the creation mechanism. MAC imports the concept when analyzing inflation. Boundary principle P3. |
| Fed operations | DEF-MON003 (mechanics of how the Fed operates) | POL deploys Fed operations as a monetary policy tool | Clean split per boundary principle P5: MON describes the mechanism (HOW the Fed works); POL describes the policy (WHEN and WHY the Fed should act). |

## 6. Real-World Hooks

| ID | Concept | Everyday Application |
|----|---------|---------------------|
| PRIM-MON001 | Money functions reasoning | Evaluating Bitcoin: is it really "money"? Three-functions test says: partial at best. |
| PRIM-MON002 | Banking system reasoning | 2008 bank runs: depositors discovered their money was not sitting in a vault -- it had been lent out. |
| PRIM-MON003 | Interest rate reasoning | Fed raises rates: your monthly mortgage payment on a $300,000 home jumps from $1,265 to $1,996. |
| PRIM-MON004 | Money supply reasoning | Fed's balance sheet grew from $900B to $9T (2008-2022); economists predicted the resulting inflation. |
| DEF-MON001 | Fractional reserve banking | Silicon Valley Bank collapse (2023): 48 hours from bank run to failure because reserves were a fraction of deposits. |
| DEF-MON002 | Money multiplier | Pre-2008 multiplier: ~9. Post-2008: ~3. Banks sat on excess reserves instead of lending, reducing money creation. |
| DEF-MON003 | Central bank operations | "The Fed raised rates" = the Fed sold bonds, pulling reserves from banks, raising the cost of overnight lending. |
| DEF-MON004 | Exchange rate | Fed raises rates above ECB's: dollar strengthens, making your European vacation cheaper but American exports pricier. |

## 7. Intra-Domain Dependency Graph

```
PRIM-MON001 (Money functions reasoning)
     |
     +---> PRIM-MON002 (Banking system reasoning)
     |          [also depends on AX-CHO001 from CHO]
     |          |
     |          +---> DEF-MON001 (Fractional reserve banking)

PRIM-MON003 (Interest rate reasoning)
     [depends on PRIM-CHO001, PRIM-CHO003 from CHO]

PRIM-MON004 (Money supply reasoning)
     [depends on PRIM-MON002, PRIM-MON003]
     |
     +---> DEF-MON002 (Money multiplier)
     |          [also depends on DEF-MON001]
     |
     +---> DEF-MON003 (Central bank operations)
     |          [also depends on PRIM-MON003, DEF-MON002]

DEF-MON004 (Exchange rate) [E]
     [depends on PRIM-MON003, PRIM-MON001]
```

**Acyclicity verification**: PRIM-MON001 and PRIM-MON003 are the two roots (both depend only on CHO imports). All arrows point from lower-depth to higher-depth items. No cycles exist. The graph is a DAG.

**Core-only subgraph**: Removing DEF-MON004 (E) leaves all Core items with satisfied dependencies. No Core item depends on DEF-MON004.

## 8. Cross-Domain Interface

### Exports

| ID | Concept | Imported by |
|----|---------|-------------|
| PRIM-MON001 | Money functions reasoning | MAC |
| PRIM-MON002 | Banking system reasoning | MAC, POL |
| PRIM-MON003 | Interest rate reasoning | MAC, POL |
| PRIM-MON004 | Money supply reasoning | MAC, POL |
| DEF-MON001 | Fractional reserve banking | POL |
| DEF-MON002 | Money multiplier | POL |
| DEF-MON003 | Central bank operations | POL |
| DEF-MON004 | Exchange rate | MAC, POL |

### Imports

| DEP ID | Imported Item | From Domain | Used by |
|--------|---------------|-------------|---------|
| DEP-MON001 | PRIM-CHO001 (Scarcity reasoning) | CHO | Loanable funds are scarce |
| DEP-MON002 | PRIM-CHO003 (Marginal analysis) | CHO | Borrowing/lending involve marginal comparisons |
| DEP-MON003 | AX-CHO001 (Rational self-interest) | CHO | Banks maximize profit; agents seek best rates |

## 9. Difficulty Tiers

| ID | Concept | Tier | Justification |
|----|---------|------|---------------|
| PRIM-MON001 | Money functions reasoning | C | Foundational: defines what money IS; required for all subsequent MON reasoning |
| PRIM-MON002 | Banking system reasoning | C | Core mechanism: explains how banks create money; prerequisite for multiplier and central bank reasoning |
| PRIM-MON003 | Interest rate reasoning | C | Core price concept: the interest rate is the most important price in the economy; connects MON to MAC and POL |
| PRIM-MON004 | Money supply reasoning | C | Core aggregate: connects the monetary base to the total money supply; essential for inflation analysis |
| DEF-MON001 | Fractional reserve banking | C | Core institutional knowledge: explains bank vulnerability (runs) and the deposit insurance system |
| DEF-MON002 | Money multiplier | C | Core quantitative tool: connects central bank actions to total money supply |
| DEF-MON003 | Central bank operations | C | Core institutional knowledge: essential for understanding Fed decisions that dominate economic news |
| DEF-MON004 | Exchange rate | E | Enrichment: important for international context but not required by any Core downstream item |

**Tier constraint verification**: The sole Enrichment item is DEF-MON004 (Exchange rate). No Core item depends on DEF-MON004. The 7 Core items form a self-contained, dependency-complete sub-taxonomy.

## 10. Self-Audit Checklist

- [x] Every PRIM has: reasoning move formulation, description, semi-formal statement, depends, ownership, source, referenced-by, tier, real-world hook
- [x] Every DEF depends only on previously listed PRIM/DEF (verified via dependency graph)
- [x] Every cross-domain reference uses full `{Type}-{Code}{Number}` format
- [x] Every import is listed in CHO's exports (PRIM-CHO001, PRIM-CHO003, AX-CHO001 all verified)
- [x] Dissolution argument is present and non-trivial (multiple sentences; banks-create-money insight; independence from GDP measurement)
- [x] Real-world hooks cover everyday non-major contexts (Bitcoin, bank runs, mortgage rates, Fed decisions, SVB collapse, European vacations)
- [x] Intra-domain dependency graph is acyclic (two roots; all edges point downward)
- [x] Tier annotations (C/E) are present on all 8 items
- [x] No PRIM/DEF duplicates an entry in another domain (checked against Primitive Registry)
- [x] Reasoning moves are genuinely "Given X, do Y" cognitive operations
