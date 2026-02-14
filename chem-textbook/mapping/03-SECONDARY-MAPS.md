# Secondary Source Maps: Saylor GOB + Chemistry in Context

**Sources mapped:** 2 (Saylor GOB, Chemistry in Context 10e)
**Template:** S3-EXT-LIGHT (chapter-level, 6 fields per entry)
**Date:** 2026-02-14
**Depends on:** 00-SOURCE-VERIFICATION.md (source metadata), 01-OPENSTAX-MAP.md (primary map), taxonomy/CONVENTIONS.md (ID registry)

---

## Purpose

This document provides chapter-level taxonomy mappings for two secondary sources that complement the primary OpenStax Chemistry 2e map:

1. **Saylor GOB** (Ball et al.) -- a one-semester non-majors GOB textbook. Its chapter sequence provides an independent validation of our domain ordering and scope boundaries, especially for organic and biological chemistry coverage that OpenStax handles at majors depth.

2. **Chemistry in Context 10e** (ACS) -- the gold-standard context-driven non-majors text. Its "need-to-know" architecture inverts the traditional topic-first approach: chemistry is introduced only when a societal issue demands it. CIC chapter-level mapping validates our composition patterns (CP-001 through CP-007) and confirms that our taxonomy items are the conceptual primitives that CIC's contexts deploy.

Neither source receives section-level mapping. Saylor is CC-BY-NC-SA (adaptable but not for direct CC-BY reuse); CIC is proprietary (structural alignment only, no content adaptation).

---

## S3-EXT-LIGHT Template

```
### {src-id}/ch{NN} --- {Chapter Title}
- **Source**: {SRC code}, Ch N
- **Domains deployed**: {list}
- **Key taxonomy items**: {IDs}
- **Application context**: {real-world theme, if applicable}
- **Composition patterns**: {CP-0NN IDs, if applicable}
- **Notes**: {alignment observations}
```

---

## Part A: Saylor GOB (Ball et al.)

**Full title:** The Basics of General, Organic, and Biological Chemistry v1.0
**Authors:** David W. Ball, John W. Hill, Rhonda J. Scott
**URL:** https://saylordotorg.github.io/text_the-basics-of-general-organic-and-biological-chemistry/
**License:** CC-BY-NC-SA (via Saylor Foundation / FlatWorld v1.0)
**Code:** SAY
**Chapters:** 20 (Ch 1--11 General, Ch 12--15 Organic, Ch 16--20 Biological)

---

### say/ch01 --- Chemistry, Matter, and Measurement
- **Source**: SAY, Ch 1
- **Domains deployed**: COM, SCL
- **Key taxonomy items**: PRIM-COM004 (substance classification), PRIM-SCL006 (unit analysis), PRIM-SCL005 (proportional reasoning), PRIM-SCL001 (macro-to-submicro translation)
- **Application context**: Everyday measurement, cooking conversions, medicine dosing
- **Composition patterns**: --
- **Notes**: Closely parallels OS Ch 1. Calibrated for non-majors from the start -- measurement is introduced through health and cooking contexts rather than laboratory technique. Good independent validation that COM + SCL are the entry-point domains.

### say/ch02 --- Elements, Atoms, and the Periodic Table
- **Source**: SAY, Ch 2
- **Domains deployed**: COM
- **Key taxonomy items**: PRIM-COM001 (atomic composition analysis), PRIM-COM002 (elemental identity), PRIM-COM003 (periodic position reasoning), PRIM-COM007 (valence electron reasoning), DEF-COM001 (isotope), DEF-COM002 (ion)
- **Application context**: Consumer electronics (element scarcity), medical imaging isotopes
- **Composition patterns**: --
- **Notes**: Comprehensive COM domain coverage in one chapter. Parallels OS Ch 2 + Ch 6.5. Saylor omits quantum mechanics entirely -- electron configurations are replaced by "number of valence electrons from group number," which aligns exactly with our non-majors calibration.

### say/ch03 --- Ionic Bonding and Simple Ionic Compounds
- **Source**: SAY, Ch 3
- **Domains deployed**: STR, COM
- **Key taxonomy items**: PRIM-STR001 (bond type classification), DEF-COM002 (ion), DEF-COM005 (electronegativity), DEF-STR009 (metallic structure)
- **Application context**: Table salt, mineral supplements, road de-icing
- **Composition patterns**: --
- **Notes**: Covers ionic bonding at non-majors depth. Includes metallic bonding overview -- one of the few sources that addresses DEF-STR009 (metallic structure, E-tier), which is missing from OpenStax's non-majors-relevant sections. Nomenclature is present but lighter than OS Ch 2.7.

### say/ch04 --- Covalent Bonding and Simple Molecular Compounds
- **Source**: SAY, Ch 4
- **Domains deployed**: STR
- **Key taxonomy items**: PRIM-STR001 (bond type classification), PRIM-STR002 (bond polarity reasoning), PRIM-STR003 (molecular shape reasoning), DEF-STR001 (Lewis structure), DEF-STR002 (molecular polarity)
- **Application context**: Water polarity, household chemicals
- **Composition patterns**: --
- **Notes**: Parallels OS Ch 7. VSEPR and Lewis structures presented at appropriate non-majors depth. Saylor combines ionic (Ch 3) and covalent (Ch 4) bonding into a natural two-chapter sequence that maps cleanly onto PRIM-STR001's bond type classification.

### say/ch05 --- Introduction to Chemical Reactions
- **Source**: SAY, Ch 5
- **Domains deployed**: CHG, COM
- **Key taxonomy items**: PRIM-CHG001 (equation reading and balancing), PRIM-CHG002 (reaction type recognition), PRIM-COM006 (conservation of atoms)
- **Application context**: Combustion, rusting, cooking transformations
- **Composition patterns**: --
- **Notes**: Parallels OS Ch 4.1--4.2. Balanced equations and reaction classification without stoichiometric calculations. Non-majors calibrated: the focus is on reading and interpreting equations, not solving mole-ratio problems. Validates our decision to separate PRIM-CHG001 (qualitative equation reading) from quantitative stoichiometry.

### say/ch06 --- Quantities in Chemical Reactions
- **Source**: SAY, Ch 6
- **Domains deployed**: SCL, COM
- **Key taxonomy items**: PRIM-SCL002 (mole concept), PRIM-SCL005 (proportional reasoning), PRIM-COM005 (chemical formula reading), DEF-COM003 (molecular vs empirical formula), DEF-COM004 (percent composition)
- **Application context**: Food labels (percent composition), pharmaceutical dosing
- **Composition patterns**: --
- **Notes**: Parallels OS Ch 3. Mole concept and formula calculations. Saylor keeps computational depth lighter than OpenStax -- more conceptual emphasis on "why the mole matters" than on multi-step calculations. The E-tier items (DEF-COM003, DEF-COM004) are present but not emphasized.

### say/ch07 --- Energy and Chemical Processes
- **Source**: SAY, Ch 7
- **Domains deployed**: NRG
- **Key taxonomy items**: PRIM-NRG001 (energy tracking), PRIM-NRG002 (bond energy reasoning), PRIM-NRG003 (exo/endothermic classification), DEF-NRG001 (heat vs temperature), DEF-NRG002 (specific heat capacity), DEF-NRG003 (enthalpy change), DEF-NRG005 (calorie/joule)
- **Application context**: Food energy, hand warmers, cold packs
- **Composition patterns**: CP-006 (food chemistry -- energy portion)
- **Notes**: Parallels OS Ch 5. Comprehensive NRG domain chapter. Saylor's calorie-focused framing (food energy, body metabolism) is more non-majors appropriate than OpenStax's thermochemistry-first approach. Excellent source for CP-006 food chemistry energy reasoning.

### say/ch08 --- Solids, Liquids, and Gases
- **Source**: SAY, Ch 8
- **Domains deployed**: STR, SCL, NRG
- **Key taxonomy items**: PRIM-STR004 (IMF hierarchy), PRIM-STR005 (structure-to-property inference), DEF-STR003 (hydrogen bond), DEF-STR006 (phase from IMF balance), DEF-SCL003 (ideal gas reasoning), PRIM-SCL001 (macro-to-submicro translation)
- **Application context**: Weather, cooking at altitude, blood pressure
- **Composition patterns**: CP-001 (structure-to-property prediction)
- **Notes**: Combines OS Ch 9 (gases) + Ch 10 (liquids/solids) into one chapter. IMF hierarchy and phase behavior are presented together, which directly mirrors CP-001's reasoning chain. The gas law treatment is conceptual rather than computational -- aligned with DEF-SCL003 at E-tier.

### say/ch09 --- Solutions
- **Source**: SAY, Ch 9
- **Domains deployed**: STR, SCL
- **Key taxonomy items**: DEF-STR004 ("like dissolves like"), DEF-STR010 (water as solvent), PRIM-SCL003 (concentration reasoning), DEF-SCL001 (molarity), DEF-SCL002 (parts per million/billion), DEF-SCL004 (colligative properties)
- **Application context**: Water purification, IV solutions, ocean salinity
- **Composition patterns**: CP-001 (structure-to-property -- solubility), CP-005 (dose makes the poison -- concentration)
- **Notes**: Parallels OS Ch 11. Saylor includes ppm/ppb in the solutions chapter with water quality examples -- strong alignment with CP-005 and DEF-SCL002. Colligative properties (E-tier) are present but brief.

### say/ch10 --- Acids and Bases
- **Source**: SAY, Ch 10
- **Domains deployed**: CHG, SCL
- **Key taxonomy items**: PRIM-CHG005 (acid-base reasoning), DEF-CHG002 (pH scale), PRIM-CHG003 (equilibrium reasoning), DEF-CHG003 (Le Chatelier's principle), PRIM-SCL003 (concentration reasoning)
- **Application context**: Stomach acid, antacids, blood pH, cleaning products
- **Composition patterns**: CP-003 (acid-base in the body)
- **Notes**: Parallels OS Ch 14 (partial). Saylor devotes an entire chapter to acids and bases at non-majors depth -- no Ka calculations, no titration curves. Buffer concept is presented through blood pH regulation, directly deploying CP-003. Excellent non-majors calibration.

### say/ch11 --- Nuclear Chemistry
- **Source**: SAY, Ch 11
- **Domains deployed**: CHG, NRG, SCL
- **Key taxonomy items**: PRIM-CHG007 (nuclear change reasoning), DEF-CHG004 (half-life), PRIM-NRG001 (energy tracking), DEF-SCL005 (safety and risk reasoning)
- **Application context**: Medical imaging, carbon dating, nuclear power, radiation safety
- **Composition patterns**: CP-002 (energy-driven transformation -- nuclear variant)
- **Notes**: Parallels OS Ch 21. Saylor gives nuclear chemistry full chapter treatment with strong non-majors hooks: medical applications, food irradiation, radiation dose. Safety/risk reasoning (DEF-SCL005) is explicitly addressed. Half-life presented conceptually rather than through exponential calculations.

### say/ch12 --- Organic Chemistry: Alkanes and Halogenated Hydrocarbons
- **Source**: SAY, Ch 12
- **Domains deployed**: STR, COM
- **Key taxonomy items**: DEF-STR007 (carbon backbone reasoning), DEF-STR005 (isomer recognition), PRIM-COM007 (valence electron reasoning), PRIM-STR001 (bond type classification)
- **Application context**: Fossil fuels, refrigerants, anesthetics
- **Composition patterns**: --
- **Notes**: First of the organic chemistry chapters. Parallels OS Ch 20.1 but with more depth on alkane naming and halogenated compounds. Carbon backbone reasoning (DEF-STR007) is the primary structural primitive deployed. Non-majors depth: functional group recognition without reaction mechanisms.

### say/ch13 --- Unsaturated and Aromatic Hydrocarbons
- **Source**: SAY, Ch 13
- **Domains deployed**: STR
- **Key taxonomy items**: DEF-STR007 (carbon backbone reasoning), DEF-STR005 (isomer recognition), PRIM-STR001 (bond type classification)
- **Application context**: Fats and oils (saturated vs unsaturated), benzene in industry
- **Composition patterns**: --
- **Notes**: Extends carbon backbone reasoning to double/triple bonds and aromatic rings. The saturated vs unsaturated fat distinction is a high-value non-majors hook that directly deploys PRIM-STR001 (bond type: single vs double bonds) and previews CP-006 (food chemistry).

### say/ch14 --- Organic Compounds of Oxygen
- **Source**: SAY, Ch 14
- **Domains deployed**: STR, CHG
- **Key taxonomy items**: DEF-STR007 (carbon backbone reasoning), PRIM-STR005 (structure-to-property inference), PRIM-CHG005 (acid-base reasoning)
- **Application context**: Alcohol metabolism, fermentation, food flavoring (esters)
- **Composition patterns**: CP-006 (food chemistry -- organic portion)
- **Notes**: Covers alcohols, ethers, aldehydes, ketones, carboxylic acids, esters. Parallels OS Ch 20.2--20.3. Structure-to-property is the main reasoning move: hydroxyl groups make alcohols water-soluble, carboxylic acids are weak acids. Non-majors emphasis on recognition and properties rather than synthesis.

### say/ch15 --- Organic Acids and Bases and Some of Their Derivatives
- **Source**: SAY, Ch 15
- **Domains deployed**: STR, CHG
- **Key taxonomy items**: DEF-STR007 (carbon backbone reasoning), PRIM-CHG005 (acid-base reasoning), PRIM-STR005 (structure-to-property inference), DEF-STR008 (polymer reasoning)
- **Application context**: Aspirin, nylon, polyester, soaps and detergents
- **Composition patterns**: CP-003 (acid-base -- pharmaceutical), CP-005 (dose makes the poison -- drug dosing)
- **Notes**: Covers esters, amines, amides, and introduces condensation polymerization. This is one of two Saylor chapters that address DEF-STR008 (polymer reasoning), which is missing from OpenStax's non-majors-relevant sections. Pharmaceutical context (aspirin, acetaminophen) directly supports CP-003 and CP-005.

### say/ch16 --- Carbohydrates
- **Source**: SAY, Ch 16
- **Domains deployed**: STR, COM, NRG
- **Key taxonomy items**: DEF-STR007 (carbon backbone reasoning), DEF-STR005 (isomer recognition), DEF-STR008 (polymer reasoning), PRIM-NRG002 (bond energy reasoning), PRIM-COM005 (chemical formula reading)
- **Application context**: Sugars in diet, fiber, diabetes and blood glucose
- **Composition patterns**: CP-006 (food chemistry), CP-007 (biochemistry connection)
- **Notes**: First biological chemistry chapter. Monosaccharides, disaccharides, polysaccharides presented as a polymer reasoning sequence (monomer to polymer). Isomer recognition deployed for glucose vs fructose vs galactose. Food energy context naturally deploys CP-006.

### say/ch17 --- Lipids
- **Source**: SAY, Ch 17
- **Domains deployed**: STR, NRG, SCL
- **Key taxonomy items**: PRIM-STR004 (IMF hierarchy), PRIM-STR005 (structure-to-property inference), DEF-STR007 (carbon backbone reasoning), PRIM-NRG002 (bond energy reasoning), PRIM-SCL004 (emergent property reasoning)
- **Application context**: Dietary fats, cholesterol, cell membranes, soap-making
- **Composition patterns**: CP-001 (structure-to-property -- fat properties), CP-006 (food chemistry -- lipid energy)
- **Notes**: Saturated vs unsaturated fats are a direct application of PRIM-STR001 and PRIM-STR004: more unsaturation means kinks in the carbon chain, weaker London dispersion forces, lower melting point (liquid oils vs solid fats). Cell membrane structure is an emergent property (PRIM-SCL004) of lipid bilayer self-assembly.

### say/ch18 --- Amino Acids, Proteins, and Enzymes
- **Source**: SAY, Ch 18
- **Domains deployed**: STR, CHG, SCL
- **Key taxonomy items**: DEF-STR007 (carbon backbone reasoning), DEF-STR008 (polymer reasoning), PRIM-STR004 (IMF hierarchy), PRIM-STR005 (structure-to-property inference), DEF-CHG001 (catalyst -- enzymes), PRIM-CHG004 (rate reasoning), PRIM-SCL004 (emergent property reasoning)
- **Application context**: Nutrition, enzyme function, drug design, denaturation (cooking eggs)
- **Composition patterns**: CP-007 (biochemistry connection)
- **Notes**: Core chapter for CP-007. Protein folding as structure-to-property inference; enzymes as biological catalysts that accelerate reaction rates. Polymer reasoning (amino acid monomers to polypeptide chain). Denaturation as a non-majors-accessible demonstration of IMF importance.

### say/ch19 --- Nucleic Acids
- **Source**: SAY, Ch 19
- **Domains deployed**: STR, SCL
- **Key taxonomy items**: DEF-STR007 (carbon backbone reasoning), DEF-STR008 (polymer reasoning), PRIM-STR004 (IMF hierarchy -- H-bonding in base pairs), DEF-STR003 (hydrogen bond), PRIM-SCL004 (emergent property reasoning)
- **Application context**: Genetics, DNA testing, genetic engineering, forensic science
- **Composition patterns**: CP-007 (biochemistry connection)
- **Notes**: DNA double helix as the primary application of CP-007. Hydrogen bonding between complementary bases is the central structural concept. Information storage as emergent property. RNA and protein synthesis provide the functional context.

### say/ch20 --- Energy Metabolism
- **Source**: SAY, Ch 20
- **Domains deployed**: NRG, CHG, COM, SCL
- **Key taxonomy items**: PRIM-NRG001 (energy tracking), PRIM-NRG002 (bond energy reasoning), PRIM-NRG003 (exo/endothermic classification), PRIM-COM006 (conservation of atoms), PRIM-CHG006 (oxidation-reduction reasoning), PRIM-SCL002 (mole concept), DEF-NRG005 (calorie/joule)
- **Application context**: ATP, cellular respiration, exercise physiology, diet and metabolism
- **Composition patterns**: CP-002 (energy-driven transformation), CP-006 (food chemistry -- metabolic capstone)
- **Notes**: Capstone chapter integrating NRG, CHG, COM, and SCL. Metabolism as oxidation-reduction (PRIM-CHG006): food molecules are oxidized, oxygen is reduced, energy is released. Conservation of atoms (PRIM-COM006) tracks carbon from glucose to CO2. This chapter is the fullest single-chapter deployment of CP-006 in any of our sources.

---

## Part B: Chemistry in Context 10e (ACS)

**Full title:** Chemistry in Context: Applying Chemistry to Society, 10th Edition
**Publisher:** McGraw-Hill / American Chemical Society
**License:** Proprietary (chapter-level structural mapping only; no content adaptation)
**Code:** CIC
**Chapters:** 14

**Pedagogical architecture:** CIC uses a "need-to-know" approach. Each chapter opens with a societal issue; the chemistry required to understand it is introduced within that chapter. Core topics are distributed across chapters rather than front-loaded. This means the same taxonomy item may appear in multiple CIC chapters, introduced at increasing depth as contexts demand it.

---

### cic/ch01 --- Portable Electronics: The Periodic Table in the Palm of Your Hand
- **Source**: CIC, Ch 1
- **Domains deployed**: COM
- **Key taxonomy items**: PRIM-COM001 (atomic composition analysis), PRIM-COM002 (elemental identity), PRIM-COM003 (periodic position reasoning), DEF-COM001 (isotope), DEF-COM002 (ion)
- **Application context**: Smartphones, rare earth elements, battery materials, electronic waste
- **Composition patterns**: --
- **Notes**: CIC introduces atomic structure and the periodic table through consumer electronics -- a highly engaging non-majors hook. Coverage closely parallels our COM domain. The "need-to-know" motivation: you need to understand elements and periodic trends to understand what is inside your phone and why certain materials are scarce.

### cic/ch02 --- The Air We Breathe
- **Source**: CIC, Ch 2
- **Domains deployed**: COM, STR
- **Key taxonomy items**: PRIM-COM005 (chemical formula reading), PRIM-STR001 (bond type classification), PRIM-STR002 (bond polarity reasoning), DEF-STR001 (Lewis structure)
- **Application context**: Air quality, pollutants (CO, O3, NOx, SO2), indoor air quality
- **Composition patterns**: --
- **Notes**: Molecular formulas and Lewis structures are introduced because understanding air quality requires knowing what molecules like O3 and CO are. Bond polarity reasoning is deployed to explain why some atmospheric molecules are reactive (O3) while others are stable (N2). Validates our COM-then-STR pedagogical ordering.

### cic/ch03 --- Radiation from the Sun
- **Source**: CIC, Ch 3
- **Domains deployed**: NRG, STR
- **Key taxonomy items**: PRIM-NRG002 (bond energy reasoning -- photon absorption), PRIM-STR002 (bond polarity reasoning), PRIM-STR003 (molecular shape reasoning)
- **Application context**: UV radiation, ozone layer, sunscreen, skin cancer
- **Composition patterns**: CP-004 (greenhouse effect -- precursor: radiation-molecule interaction)
- **Notes**: Electromagnetic spectrum and photon energy are introduced to explain UV damage and ozone chemistry. This chapter lays groundwork for CP-004 by establishing how molecular structure determines radiation absorption. The "need-to-know" motivation: understanding sunscreen requires understanding how molecules absorb UV.

### cic/ch04 --- Climate Change
- **Source**: CIC, Ch 4
- **Domains deployed**: STR, NRG, SCL
- **Key taxonomy items**: PRIM-STR003 (molecular shape reasoning), PRIM-STR002 (bond polarity reasoning), PRIM-NRG002 (bond energy reasoning -- IR absorption), PRIM-SCL004 (emergent property reasoning), DEF-SCL002 (parts per million/billion)
- **Application context**: Greenhouse effect, carbon footprint, CO2 concentration trends, climate policy
- **Composition patterns**: CP-004 (greenhouse effect)
- **Notes**: The single best external validation of CP-004. CIC Ch 4 deploys exactly the primitives our composition pattern identifies: molecular shape and bond polarity determine IR activity (STR), bond vibration absorbs IR energy (NRG), and ppm-level concentrations produce planetary-scale warming (SCL). This chapter demonstrates that CP-004 is not our invention but a natural reasoning chain that CIC arrives at independently.

### cic/ch05 --- Energy from Combustion
- **Source**: CIC, Ch 5
- **Domains deployed**: NRG, CHG, COM
- **Key taxonomy items**: PRIM-NRG001 (energy tracking), PRIM-NRG002 (bond energy reasoning), PRIM-NRG003 (exo/endothermic classification), DEF-NRG003 (enthalpy change), PRIM-CHG001 (equation reading and balancing), PRIM-COM006 (conservation of atoms)
- **Application context**: Fossil fuels, combustion engines, coal power, energy density
- **Composition patterns**: CP-002 (energy-driven transformation)
- **Notes**: Thermochemistry is introduced because understanding fossil fuels requires energy accounting. Combustion reactions deploy equation balancing (CHG), exo/endothermic classification (NRG), and atom conservation (COM). Enthalpy is introduced as "heat released per gram of fuel" -- a non-majors-calibrated framing. Strong CP-002 deployment.

### cic/ch06 --- Energy from Alternative Sources
- **Source**: CIC, Ch 6
- **Domains deployed**: CHG, NRG, SCL
- **Key taxonomy items**: PRIM-CHG007 (nuclear change reasoning), DEF-CHG004 (half-life), PRIM-NRG001 (energy tracking), DEF-SCL005 (safety and risk reasoning), PRIM-CHG006 (oxidation-reduction reasoning)
- **Application context**: Nuclear power, solar cells, hydrogen fuel, wind energy, risk assessment
- **Composition patterns**: CP-002 (energy-driven transformation -- nuclear and alternative variants)
- **Notes**: Nuclear chemistry is introduced as an energy source rather than a standalone topic. Fission/fusion, half-life, and radiation safety are deployed because the societal question ("should we use nuclear power?") demands them. CIC also introduces solar and hydrogen energy, connecting to redox reasoning. DEF-SCL005 (safety/risk) is directly exercised through nuclear waste and radiation dose discussions.

### cic/ch07 --- Energy Storage
- **Source**: CIC, Ch 7
- **Domains deployed**: CHG, NRG
- **Key taxonomy items**: PRIM-CHG006 (oxidation-reduction reasoning), PRIM-NRG001 (energy tracking), PRIM-NRG003 (exo/endothermic classification), PRIM-NRG005 (spontaneity reasoning)
- **Application context**: Batteries (Li-ion, lead-acid), fuel cells, electric vehicles, grid storage
- **Composition patterns**: CP-002 (energy-driven transformation)
- **Notes**: Electrochemistry through the lens of energy storage technology. Redox reasoning is the central primitive: batteries convert chemical energy to electrical energy via electron transfer. CIC introduces oxidation states and half-reactions at the level needed to understand a battery, not at the level needed to balance complex redox equations. Excellent deployment of CP-002 with the "why does a battery die?" hook from ADP-002.

### cic/ch08 --- Water Everywhere: A Most Precious Resource
- **Source**: CIC, Ch 8
- **Domains deployed**: STR, CHG, SCL
- **Key taxonomy items**: DEF-STR003 (hydrogen bond), DEF-STR004 ("like dissolves like"), DEF-STR010 (water as solvent), PRIM-CHG005 (acid-base reasoning), DEF-CHG002 (pH scale), PRIM-SCL003 (concentration reasoning), DEF-SCL001 (molarity), DEF-SCL002 (parts per million/billion)
- **Application context**: Water quality, purification, contamination (lead, arsenic), ocean acidification
- **Composition patterns**: CP-003 (acid-base -- water quality), CP-005 (dose makes the poison -- contaminants)
- **Notes**: The most domain-rich CIC chapter, deploying STR, CHG, and SCL together. Water's unique properties (H-bonding), dissolution (like dissolves like), acid-base chemistry (pH of water sources), and concentration (ppm of contaminants) are all introduced because water quality demands them. Directly exercises CP-003 and CP-005. The ocean acidification discussion is a powerful real-world deployment of acid-base + concentration reasoning.

### cic/ch09 --- The World of Polymers and Plastics
- **Source**: CIC, Ch 9
- **Domains deployed**: STR, SCL
- **Key taxonomy items**: DEF-STR007 (carbon backbone reasoning), DEF-STR008 (polymer reasoning), DEF-STR005 (isomer recognition), PRIM-STR005 (structure-to-property inference), PRIM-SCL004 (emergent property reasoning)
- **Application context**: Plastic recycling, biodegradable polymers, microplastics, sustainability
- **Composition patterns**: CP-001 (structure-to-property -- polymer properties)
- **Notes**: This chapter is the primary external source for DEF-STR008 (polymer reasoning), which is absent from OpenStax's non-majors-relevant sections. Organic chemistry is introduced to the degree needed to understand polymerization: carbon backbone, functional groups, addition vs condensation polymers. Structure-to-property reasoning is deployed to explain why different plastics have different properties (flexible vs rigid, recyclable vs not).

### cic/ch10 --- Brewing and Chewing
- **Source**: CIC, Ch 10
- **Domains deployed**: STR, CHG, NRG
- **Key taxonomy items**: DEF-STR007 (carbon backbone reasoning), PRIM-STR005 (structure-to-property inference), PRIM-CHG004 (rate reasoning), PRIM-NRG006 (activation energy reasoning), DEF-CHG001 (catalyst -- fermentation enzymes)
- **Application context**: Fermentation, baking, food additives, flavor chemistry
- **Composition patterns**: CP-006 (food chemistry)
- **Notes**: Food science as chemistry context. Fermentation is introduced as a chemical reaction with rate and catalyst reasoning. Functional groups (alcohols, acids, esters) are deployed because understanding flavor and food processing requires them. Directly exercises CP-006. The "need-to-know" approach is particularly effective here: students learn organic functional groups to understand what makes vinegar sour and bread rise.

### cic/ch11 --- Nutrition
- **Source**: CIC, Ch 11
- **Domains deployed**: COM, NRG, CHG, SCL
- **Key taxonomy items**: PRIM-COM006 (conservation of atoms), PRIM-NRG002 (bond energy reasoning), PRIM-NRG003 (exo/endothermic classification), DEF-NRG005 (calorie/joule), PRIM-SCL002 (mole concept), PRIM-SCL005 (proportional reasoning), DEF-STR007 (carbon backbone reasoning)
- **Application context**: Food labels, Calories, macronutrients, vitamins, dietary guidelines
- **Composition patterns**: CP-006 (food chemistry -- full deployment)
- **Notes**: The fullest CIC deployment of CP-006. Carbohydrates, fats, and proteins are introduced as energy sources whose caloric content reflects bond energy. Conservation of atoms is invoked to trace food molecules through metabolism. CIC's quantitative reasoning (reading food labels, computing caloric intake) deploys PRIM-SCL005 and DEF-NRG005 in a deeply non-majors-relevant context.

### cic/ch12 --- Health and Medicine
- **Source**: CIC, Ch 12
- **Domains deployed**: STR, CHG, SCL
- **Key taxonomy items**: PRIM-STR005 (structure-to-property inference), DEF-STR005 (isomer recognition), PRIM-CHG004 (rate reasoning), DEF-CHG001 (catalyst -- enzyme inhibition), PRIM-SCL003 (concentration reasoning), DEF-SCL005 (safety and risk reasoning)
- **Application context**: Pharmaceuticals, drug design, chirality, antibiotic resistance, dosing
- **Composition patterns**: CP-005 (dose makes the poison), CP-007 (biochemistry connection -- drug-enzyme interaction)
- **Notes**: Structure-to-property inference is the central reasoning move: drug molecules are designed so their 3D shape matches a target enzyme or receptor. Chirality (a special case of isomer recognition, DEF-STR005) explains why mirror-image molecules can have different biological effects. Dose-response reasoning (CP-005) is directly invoked for drug safety. CIC's treatment of drug chemistry is a model of need-to-know pedagogy.

### cic/ch13 --- Genes and Life
- **Source**: CIC, Ch 13
- **Domains deployed**: STR, CHG, SCL
- **Key taxonomy items**: DEF-STR007 (carbon backbone reasoning), DEF-STR008 (polymer reasoning), PRIM-STR004 (IMF hierarchy -- H-bonding in DNA), DEF-STR003 (hydrogen bond), PRIM-STR005 (structure-to-property inference), PRIM-SCL004 (emergent property reasoning)
- **Application context**: Genetics, GMOs, gene therapy, forensic DNA, CRISPR
- **Composition patterns**: CP-007 (biochemistry connection)
- **Notes**: Full deployment of CP-007 in a societal context. DNA structure, protein synthesis, and genetic engineering are introduced because understanding genetic technology requires molecular reasoning. CIC's treatment parallels our ADP-007 reasoning chain almost exactly: polymer structure provides the backbone, hydrogen bonding determines 3D shape, structure dictates function, and biological capability is emergent.

### cic/ch14 --- Who Killed Dr. Thompson? A Forensic Mystery
- **Source**: CIC, Ch 14
- **Domains deployed**: MULTI (all domains)
- **Key taxonomy items**: (integrative -- draws from all 5 domains)
- **Application context**: Forensic science, toxicology, analytical chemistry, mystery narrative
- **Composition patterns**: CP-005 (dose makes the poison -- toxicology)
- **Notes**: Capstone chapter that integrates chemistry from all preceding chapters into a forensic investigation narrative. Students deploy composition analysis (COM), structural identification (STR), energy reasoning (NRG), chemical change reasoning (CHG), and quantitative methods (SCL) to solve a mystery. Validates our claim that all 5 domains are needed for complete chemical reasoning. The narrative structure is a powerful engagement tool for non-majors.

---

## Part C: Cross-Source Comparison

### Domain Coverage Comparison

| Domain | OpenStax 2e (OS) | Saylor GOB (SAY) | CIC 10e | Our Taxonomy |
|--------|-----------------|-------------------|---------|-------------|
| COM (13 items) | 12/13 | 12/13 | 7/13 | 13 |
| STR (15 items) | 13/15 | 15/15 | 12/15 | 15 |
| NRG (11 items) | 11/11 | 8/11 | 7/11 | 11 |
| CHG (12 items) | 12/12 | 10/12 | 10/12 | 12 |
| SCL (11 items) | 11/11 | 10/11 | 9/11 | 11 |
| **Total** | **59/62** | **55/62** | **45/62** | **62** |

**Notes on coverage gaps:**
- **OS missing (3):** PRIM-COM008 (meta-cognitive), DEF-STR008 (polymer), DEF-STR009 (metallic). Covered by SAY and CIC.
- **SAY missing (7):** PRIM-COM008 (meta-cognitive), PRIM-NRG004 (entropy), PRIM-NRG005 (spontaneity), DEF-NRG004 (free energy), DEF-CHG003 (Le Chatelier's -- implicit only), DEF-CHG005 (precipitation), DEF-SCL003 (ideal gas -- qualitative only). GOB texts typically omit formal thermodynamics and equilibrium constants.
- **CIC missing (17):** CIC deploys fewer items total because its "need-to-know" approach only introduces chemistry that a context demands. Items like DEF-COM003 (molecular vs empirical formula), DEF-NRG002 (specific heat), and DEF-CHG005 (precipitation) are never motivated by CIC's 14 societal contexts. This is expected and validates our Enrichment tier: most missing CIC items are E-tier.

### Pedagogical Architecture Comparison

| Feature | OpenStax 2e | Saylor GOB | CIC 10e | Our Taxonomy |
|---------|-----------|------------|---------|-------------|
| **Organizing principle** | Topic-first | Topic-first (GOB sequence) | Context-first ("need-to-know") | Domain-first (reasoning moves) |
| **Audience** | Majors | Non-majors (GOB) | Non-majors (liberal arts) | Non-majors (general) |
| **Math level** | Calculus-ready | Algebra | Pre-algebra | Algebra (no calculus) |
| **Organic/bio coverage** | 1 chapter | 9 chapters (Ch 12--20) | Distributed across contexts | Extension protocol |
| **Total chapters** | 21 | 20 | 14 | 5 domains + 7 CPs |
| **Chapter ordering** | Traditional (atoms-first) | GOB standard | Societal issue-driven | Dependency DAG |
| **How cross-domain topics arise** | Implicit | Implicit | Forced by context | Explicit composition patterns |

### Composition Pattern Deployment Comparison

| Pattern | OS Chapters | SAY Chapters | CIC Chapters |
|---------|------------|-------------|-------------|
| CP-001 (Structure-to-Property) | Ch 10, 11 | Ch 8, 9, 17 | Ch 4, 9 |
| CP-002 (Energy-Driven Transformation) | Ch 5, 16, 17 | Ch 7, 11, 20 | Ch 5, 6, 7 |
| CP-003 (Acid-Base in the Body) | Ch 14 | Ch 10, 15 | Ch 8 |
| CP-004 (Greenhouse Effect) | Ch 6 (peripheral) | -- | Ch 3, 4 |
| CP-005 (Dose Makes the Poison) | Ch 3, 21 | Ch 9, 15 | Ch 8, 12, 14 |
| CP-006 (Food Chemistry) | Ch 5 (peripheral) | Ch 7, 14, 16, 20 | Ch 10, 11 |
| CP-007 (Biochemistry Connection) | Ch 20 (peripheral) | Ch 16, 17, 18, 19 | Ch 12, 13 |

---

## Part D: Key Insights

### 1. CIC's "need-to-know" approach validates composition patterns, not domain specs

CIC does not teach domains; it teaches contexts that happen to require specific domain primitives. Our composition patterns (CP-001 through CP-007) are precisely the cross-domain reasoning chains that CIC's contexts deploy. This is strong independent validation: if CIC had been designed using our taxonomy, the chapter-to-pattern mapping would look almost identical to what we observe. The fact that CIC arrives at the same reasoning chains through context-driven pedagogy confirms that our patterns capture real conceptual structure, not arbitrary groupings.

### 2. Saylor's GOB structure maps cleanly onto our domain sequence

Saylor's 20-chapter sequence follows a conventional GOB (General-Organic-Biological) arc:
- Ch 1--2: COM domain (matter, atoms, periodic table)
- Ch 3--4: STR domain (ionic and covalent bonding)
- Ch 5--6: CHG + SCL domains (reactions, quantities)
- Ch 7: NRG domain (energy)
- Ch 8--9: STR + SCL cross-domain (states, solutions)
- Ch 10: CHG domain (acids and bases)
- Ch 11: CHG + NRG (nuclear chemistry)
- Ch 12--15: STR extension (organic chemistry via carbon backbone reasoning)
- Ch 16--20: CP-006 + CP-007 deployment (biochemistry applications)

This maps onto our dependency DAG (COM then STR/NRG/SCL then CHG) with minor reordering. The organic and biological chapters (12--20) are not new domains but deployment exercises for STR, NRG, and CHG primitives in increasingly complex molecular contexts -- exactly as our extension protocol predicts.

### 3. Three-source triangulation closes all taxonomy coverage gaps

No single source covers all 62 taxonomy items at non-majors depth. But the three sources together achieve full coverage:
- **PRIM-COM008** (causal chain reasoning): Meta-cognitive, deployed implicitly by all three sources but never taught as a standalone topic. Coverage comes from our reasoning-move framing itself.
- **DEF-STR008** (polymer reasoning): SAY Ch 15 + CIC Ch 9 provide the needed coverage that OS lacks.
- **DEF-STR009** (metallic structure): SAY Ch 3 provides the coverage that OS lacks (OS covers it in the SKIPped Ch 18).

### 4. CIC systematically deploys fewer items but at higher integration

CIC covers 45/62 items versus OpenStax's 59/62, yet CIC achieves deeper cross-domain integration per chapter. A typical CIC chapter deploys 3--4 domains simultaneously because the societal context demands it. A typical OS chapter deploys 1--2 domains because the topic-first organization isolates domains. This confirms our design principle (ASM-GLB004): composition patterns, not individual primitives, are the unit of meaningful chemical reasoning for non-majors.

### 5. Saylor is the only source that covers organic and biological chemistry at non-majors depth

OpenStax's organic chemistry (Ch 20) is a single chapter written for majors. CIC distributes organic chemistry across contexts but never teaches it systematically. Saylor devotes 9 full chapters (12--20) to organic and biological chemistry at a consistent non-majors depth. For our textbook's organic and biological content -- particularly DEF-STR007 (carbon backbone), DEF-STR005 (isomer recognition), DEF-STR008 (polymer reasoning), CP-006 (food chemistry), and CP-007 (biochemistry connection) -- Saylor is the most valuable secondary source.

### 6. E-tier items cluster in sources that teach them

Our Enrichment-tier items (DEF-COM003, DEF-COM004, DEF-NRG004, DEF-SCL003, DEF-SCL004, PRIM-CHG007, DEF-CHG005, DEF-STR009) appear consistently in OpenStax and Saylor but are largely absent from CIC. This independently validates our Core/Enrichment classification: the items we flagged as "cuttable without breaking dependency chains" are exactly the items that CIC's 14-chapter, context-driven curriculum chose to cut.
