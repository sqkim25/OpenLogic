# OpenStax Chemistry 2e — Source Map

**Source:** OpenStax Chemistry 2e (CC-BY 4.0)
**Repo:** `openstax/osbooks-chemistry-bundle`
**Collection:** `chemistry-2e.collection.xml`
**Total:** 21 chapters, 114 content sections, 21 introduction modules

---

## Pass 1: Chapter Triage

Each chapter classified as:
- **RELEVANT**: Chapter covers taxonomy topics at appropriate depth. Full section mapping.
- **PARTIAL**: Mix of relevant and out-of-scope content. Section-by-section mapping.
- **SKIP**: Entirely MAJORS-ONLY or out of scope. One-line justification.

| Ch | Title | Verdict | Justification |
|----|-------|---------|---------------|
| 1 | Essential Ideas | RELEVANT | Substance classification (PRIM-COM004), measurement/unit analysis (PRIM-SCL006), physical/chemical properties. Foundation for all domains. |
| 2 | Atoms, Molecules, and Ions | RELEVANT | Atomic composition (PRIM-COM001), elemental identity (PRIM-COM002), periodic position (PRIM-COM003), chemical formulas (PRIM-COM005), valence electrons (PRIM-COM007). Core COM domain. |
| 3 | Composition of Substances and Solutions | RELEVANT | Mole concept (PRIM-SCL002), molarity (DEF-SCL001), empirical/molecular formulas (DEF-COM003), percent composition (DEF-COM004). Core SCL domain. |
| 4 | Stoichiometry of Chemical Reactions | PARTIAL | Equation reading/balancing (PRIM-CHG001) and reaction classification (PRIM-CHG002) are relevant. Reaction stoichiometry calculations, yields, and quantitative analysis exceed non-majors depth. |
| 5 | Thermochemistry | RELEVANT | Energy tracking (PRIM-NRG001), exo/endothermic (PRIM-NRG003), heat vs temperature (DEF-NRG001), specific heat (DEF-NRG002), enthalpy (DEF-NRG003). Core NRG domain. |
| 6 | Electronic Structure and Periodic Properties | PARTIAL | Periodic variations (6.5) relevant to COM. EM energy (6.1) relevant as background for STR. Bohr model, quantum theory, electron configurations are MAJORS-ONLY depth. |
| 7 | Chemical Bonding and Molecular Geometry | RELEVANT | Bond types (PRIM-STR001), bond polarity (PRIM-STR002), molecular shape (PRIM-STR003), Lewis structures (DEF-STR001), molecular polarity (DEF-STR002). Core STR domain. |
| 8 | Advanced Theories of Covalent Bonding | **SKIP** | Entirely MAJORS-ONLY: valence bond theory, hybrid orbitals, molecular orbital theory. No taxonomy items in scope. |
| 9 | Gases | PARTIAL | Gas pressure and ideal gas law relevant to DEF-SCL003 (E-tier). Kinetic-molecular theory gives conceptual background. Effusion, non-ideal behavior are MAJORS-ONLY. |
| 10 | Liquids and Solids | PARTIAL | IMF hierarchy (PRIM-STR004), phase from IMF balance (DEF-STR006), structure-to-property (PRIM-STR005) are core. Phase diagrams, lattice structures are MAJORS-ONLY. |
| 11 | Solutions and Colloids | PARTIAL | "Like dissolves like" (DEF-STR004), water as solvent (DEF-STR010), dissolution. Colligative properties (DEF-SCL004, E-tier). Colloids section is out of scope. |
| 12 | Kinetics | PARTIAL | Rate reasoning (PRIM-CHG004), collision theory/activation energy (PRIM-NRG006), catalysis (DEF-CHG001) are relevant. Rate laws, integrated rate laws, mechanisms are MAJORS-ONLY. |
| 13 | Fundamental Equilibrium Concepts | PARTIAL | Equilibrium reasoning (PRIM-CHG003), Le Chatelier's (DEF-CHG003) are C-tier. Equilibrium constants and calculations are MAJORS-ONLY depth. |
| 14 | Acid-Base Equilibria | PARTIAL | Acid-base reasoning (PRIM-CHG005), pH scale (DEF-CHG002) are C-tier. Buffers relevant to CP-003. Hydrolysis, polyprotic acids, titrations are MAJORS-ONLY. |
| 15 | Equilibria of Other Reaction Classes | PARTIAL | Precipitation (DEF-CHG005, E-tier) marginally relevant. Lewis acids/bases and coupled equilibria are MAJORS-ONLY. Lowest-priority PARTIAL chapter. |
| 16 | Thermodynamics | PARTIAL | Entropy (PRIM-NRG004), spontaneity (PRIM-NRG005), free energy (DEF-NRG004, E-tier) relevant conceptually. Mathematical depth (Gibbs calculations, 3rd law) is MAJORS-ONLY. |
| 17 | Electrochemistry | PARTIAL | Redox review (PRIM-CHG006) relevant. Batteries/fuel cells have real-world hooks (CP-002). Electrode potentials, Nernst equation, electrolysis are MAJORS-ONLY. |
| 18 | Representative Metals, Metalloids, and Nonmetals | **SKIP** | Entirely MAJORS-ONLY descriptive chemistry. 12 sections on individual element groups. No taxonomy items in scope. |
| 19 | Transition Metals and Coordination Chemistry | **SKIP** | Entirely MAJORS-ONLY: coordination chemistry, crystal field theory. No taxonomy items in scope. |
| 20 | Organic Chemistry | PARTIAL | Carbon backbone (DEF-STR007), functional groups, isomer recognition (DEF-STR005) relevant. Polymer reasoning (DEF-STR008) via Ch 9 is a stretch. Basic coverage aligns with non-majors scope. |
| 21 | Nuclear Chemistry | PARTIAL | Nuclear change (PRIM-CHG007, E-tier), half-life (DEF-CHG004), radioisotope uses, biological effects all relevant to non-majors. Structure/stability details are MAJORS-ONLY. |

### Triage Summary

| Verdict | Count | Chapters |
|---------|-------|----------|
| RELEVANT | 5 | 1, 2, 3, 5, 7 |
| PARTIAL | 13 | 4, 6, 9, 10, 11, 12, 13, 14, 15, 16, 17, 20, 21 |
| SKIP | 3 | 8, 18, 19 |

**Sections requiring mapping:** ~80 (5 RELEVANT chapters with full mapping = ~28 sections, plus relevant portions of 13 PARTIAL chapters = ~52 sections)

---

## Pass 2: Section-Level Mapping

### Template (S3-EXT, 8 fields)
```
### os/ch{NN}/{N.N} --- {Section Title}
- **Source**: OS, Ch N, Section N.N
- **File**: modules/{module_id}/index.cnxml
- **Domain**: {COM | STR | NRG | CHG | SCL | MULTI}
- **Maps to**: {taxonomy IDs}
- **Coverage depth**: {FULL | PARTIAL | PERIPHERAL}
- **Audience level**: {NON-MAJORS | MAJORS-ONLY | BOTH}
- **Content signal**: {ADAPT | REWRITE | REFERENCE-ONLY | SKIP}
- **Notes**: {observations}
```

---

### Chapter 1: Essential Ideas (RELEVANT)

### os/ch01/1.1 --- Chemistry in Context
- **Source**: OS, Ch 1, Section 1.1
- **File**: modules/m68664/index.cnxml
- **Domain**: MULTI
- **Maps to**: (introductory framing — no direct taxonomy items)
- **Coverage depth**: PERIPHERAL
- **Audience level**: BOTH
- **Content signal**: REFERENCE-ONLY
- **Notes**: Historical overview and "central science" framing. Useful motivational context but no taxonomy primitives introduced.

### os/ch01/1.2 --- Phases and Classification of Matter
- **Source**: OS, Ch 1, Section 1.2
- **File**: modules/m68667/index.cnxml
- **Domain**: COM
- **Maps to**: PRIM-COM004 (substance classification)
- **Coverage depth**: FULL
- **Audience level**: BOTH
- **Content signal**: ADAPT
- **Notes**: Pure substances vs mixtures, elements vs compounds, phases of matter. Direct coverage of PRIM-COM004. Needs reframing as a reasoning move ("Given a sample, classify its composition").

### os/ch01/1.3 --- Physical and Chemical Properties
- **Source**: OS, Ch 1, Section 1.3
- **File**: modules/m68670/index.cnxml
- **Domain**: MULTI (COM, STR)
- **Maps to**: PRIM-COM004 (substance classification), PRIM-STR005 (structure-to-property inference)
- **Coverage depth**: PARTIAL
- **Audience level**: BOTH
- **Content signal**: ADAPT
- **Notes**: Physical vs chemical properties/changes. Foundation for structure-to-property reasoning. Non-majors appropriate.

### os/ch01/1.4 --- Measurements
- **Source**: OS, Ch 1, Section 1.4
- **File**: modules/m68674/index.cnxml
- **Domain**: SCL
- **Maps to**: PRIM-SCL006 (unit analysis)
- **Coverage depth**: FULL
- **Audience level**: BOTH
- **Content signal**: ADAPT
- **Notes**: SI units, metric system, dimensional analysis. Core scaffolding for PRIM-SCL006.

### os/ch01/1.5 --- Measurement Uncertainty, Accuracy, and Precision
- **Source**: OS, Ch 1, Section 1.5
- **File**: modules/m68690/index.cnxml
- **Domain**: SCL
- **Maps to**: PRIM-SCL006 (unit analysis — peripheral)
- **Coverage depth**: PERIPHERAL
- **Audience level**: MAJORS-ONLY
- **Content signal**: REFERENCE-ONLY
- **Notes**: Significant figures and error analysis. Useful background for quantitative reasoning but depth exceeds non-majors scope. Our taxonomy handles this implicitly through proportional reasoning.

### os/ch01/1.6 --- Mathematical Treatment of Measurement Results
- **Source**: OS, Ch 1, Section 1.6
- **File**: modules/m68683/index.cnxml
- **Domain**: SCL
- **Maps to**: PRIM-SCL005 (proportional reasoning), PRIM-SCL006 (unit analysis)
- **Coverage depth**: PARTIAL
- **Audience level**: BOTH
- **Content signal**: REWRITE
- **Notes**: Dimensional analysis, unit conversions. Relevant to SCL primitives but presented as procedural math rather than reasoning moves. Needs reframing.

---

### Chapter 2: Atoms, Molecules, and Ions (RELEVANT)

### os/ch02/2.1 --- Early Ideas in Atomic Theory
- **Source**: OS, Ch 2, Section 2.1
- **File**: modules/m68685/index.cnxml
- **Domain**: COM
- **Maps to**: PRIM-COM001 (atomic composition analysis)
- **Coverage depth**: PARTIAL
- **Audience level**: BOTH
- **Content signal**: ADAPT
- **Notes**: Dalton's atomic theory, laws of definite/multiple proportions. Historical context for PRIM-COM001. Can be condensed for non-majors.

### os/ch02/2.2 --- Evolution of Atomic Theory
- **Source**: OS, Ch 2, Section 2.2
- **File**: modules/m68687/index.cnxml
- **Domain**: COM
- **Maps to**: PRIM-COM001 (atomic composition analysis)
- **Coverage depth**: PARTIAL
- **Audience level**: BOTH
- **Content signal**: REWRITE
- **Notes**: Thomson, Millikan, Rutherford experiments. Historical depth exceeds non-majors needs but proton/neutron/electron model is essential for PRIM-COM001.

### os/ch02/2.3 --- Atomic Structure and Symbolism
- **Source**: OS, Ch 2, Section 2.3
- **File**: modules/m68692/index.cnxml
- **Domain**: COM
- **Maps to**: PRIM-COM001 (atomic composition analysis), PRIM-COM002 (elemental identity), DEF-COM001 (isotope), DEF-COM002 (ion)
- **Coverage depth**: FULL
- **Audience level**: BOTH
- **Content signal**: ADAPT
- **Notes**: Atomic number, mass number, isotopes, ions. Direct and comprehensive coverage of COM fundamentals. High-value section.

### os/ch02/2.4 --- Chemical Formulas
- **Source**: OS, Ch 2, Section 2.4
- **File**: modules/m68693/index.cnxml
- **Domain**: COM
- **Maps to**: PRIM-COM005 (chemical formula reading)
- **Coverage depth**: FULL
- **Audience level**: BOTH
- **Content signal**: ADAPT
- **Notes**: Molecular formulas, empirical formulas, structural formulas. Direct coverage of PRIM-COM005.

### os/ch02/2.5 --- The Periodic Table
- **Source**: OS, Ch 2, Section 2.5
- **File**: modules/m68695/index.cnxml
- **Domain**: COM
- **Maps to**: PRIM-COM003 (periodic position reasoning)
- **Coverage depth**: FULL
- **Audience level**: BOTH
- **Content signal**: ADAPT
- **Notes**: Groups, periods, metals/nonmetals/metalloids. Core coverage of PRIM-COM003. Non-majors appropriate.

### os/ch02/2.6 --- Ionic and Molecular Compounds
- **Source**: OS, Ch 2, Section 2.6
- **File**: modules/m68696/index.cnxml
- **Domain**: MULTI (COM, STR)
- **Maps to**: PRIM-COM004 (substance classification), PRIM-STR001 (bond type classification)
- **Coverage depth**: FULL
- **Audience level**: BOTH
- **Content signal**: ADAPT
- **Notes**: Bridges COM and STR domains. Ionic vs molecular compounds, formula units vs molecules. High-value for cross-domain reasoning.

### os/ch02/2.7 --- Chemical Nomenclature
- **Source**: OS, Ch 2, Section 2.7
- **File**: modules/m68698/index.cnxml
- **Domain**: COM
- **Maps to**: PRIM-COM005 (chemical formula reading — peripheral)
- **Coverage depth**: PERIPHERAL
- **Audience level**: BOTH
- **Content signal**: REWRITE
- **Notes**: IUPAC naming rules. Non-majors need basic nomenclature (water, carbon dioxide, table salt) but not systematic naming of all compound types. Significant condensation needed.

---

### Chapter 3: Composition of Substances and Solutions (RELEVANT)

### os/ch03/3.1 --- Formula Mass and the Mole Concept
- **Source**: OS, Ch 3, Section 3.1
- **File**: modules/m68700/index.cnxml
- **Domain**: SCL
- **Maps to**: PRIM-SCL002 (mole concept), PRIM-SCL005 (proportional reasoning)
- **Coverage depth**: FULL
- **Audience level**: BOTH
- **Content signal**: REWRITE
- **Notes**: Formula mass, molar mass, Avogadro's number. Core SCL content. OpenStax presents computationally; needs reframing as a reasoning move (macro-submicro bridge).

### os/ch03/3.2 --- Determining Empirical and Molecular Formulas
- **Source**: OS, Ch 3, Section 3.2
- **File**: modules/m68702/index.cnxml
- **Domain**: COM
- **Maps to**: DEF-COM003 (molecular vs empirical formula), DEF-COM004 (percent composition)
- **Coverage depth**: FULL
- **Audience level**: BOTH
- **Content signal**: REWRITE
- **Notes**: Both DEFs are E-tier. Computational emphasis needs simplification for non-majors. Conceptual understanding of what empirical formulas tell us is more important than calculation procedures.

### os/ch03/3.3 --- Molarity
- **Source**: OS, Ch 3, Section 3.3
- **File**: modules/m68703/index.cnxml
- **Domain**: SCL
- **Maps to**: PRIM-SCL003 (concentration reasoning), DEF-SCL001 (molarity)
- **Coverage depth**: FULL
- **Audience level**: BOTH
- **Content signal**: ADAPT
- **Notes**: Molarity definition, dilution. Direct coverage of C-tier items. Non-majors appropriate at conceptual level.

### os/ch03/3.4 --- Other Units for Solution Concentrations
- **Source**: OS, Ch 3, Section 3.4
- **File**: modules/m68704/index.cnxml
- **Domain**: SCL
- **Maps to**: DEF-SCL002 (parts per million/billion), PRIM-SCL003 (concentration reasoning)
- **Coverage depth**: PARTIAL
- **Audience level**: BOTH
- **Content signal**: ADAPT
- **Notes**: Mass percent, ppm, ppb. PPM/PPB is C-tier and highly relevant for non-majors (water quality, air pollution). Mass percent and molality can be condensed.

---

### Chapter 4: Stoichiometry of Chemical Reactions (PARTIAL)

### os/ch04/4.1 --- Writing and Balancing Chemical Equations
- **Source**: OS, Ch 4, Section 4.1
- **File**: modules/m68709/index.cnxml
- **Domain**: CHG
- **Maps to**: PRIM-CHG001 (equation reading and balancing), PRIM-COM006 (conservation of atoms)
- **Coverage depth**: FULL
- **Audience level**: BOTH
- **Content signal**: ADAPT
- **Notes**: Chemical equations, balancing by inspection, conservation of mass. Core C-tier content. Non-majors need conceptual understanding of balanced equations.

### os/ch04/4.2 --- Classifying Chemical Reactions
- **Source**: OS, Ch 4, Section 4.2
- **File**: modules/m68710/index.cnxml
- **Domain**: CHG
- **Maps to**: PRIM-CHG002 (reaction type recognition), PRIM-CHG005 (acid-base), PRIM-CHG006 (oxidation-reduction)
- **Coverage depth**: FULL
- **Audience level**: BOTH
- **Content signal**: ADAPT
- **Notes**: Precipitation, acid-base, redox reaction types. Direct coverage of multiple CHG primitives. High-value section.

### os/ch04/4.3 --- Reaction Stoichiometry
- **Source**: OS, Ch 4, Section 4.3
- **File**: modules/m68713/index.cnxml
- **Domain**: SCL
- **Maps to**: PRIM-SCL005 (proportional reasoning)
- **Coverage depth**: PARTIAL
- **Audience level**: MAJORS-ONLY
- **Content signal**: REFERENCE-ONLY
- **Notes**: Mole-to-mole and mass-to-mass calculations. Computational depth exceeds non-majors scope. Conceptual idea (ratios in reactions) covered by PRIM-SCL005.

### os/ch04/4.4 --- Reaction Yields
- **Source**: OS, Ch 4, Section 4.4
- **File**: modules/m68714/index.cnxml
- **Domain**: SCL
- **Maps to**: (no direct taxonomy items)
- **Coverage depth**: PERIPHERAL
- **Audience level**: MAJORS-ONLY
- **Content signal**: SKIP
- **Notes**: Theoretical/actual/percent yield. Entirely MAJORS-ONLY computational chemistry.

### os/ch04/4.5 --- Quantitative Chemical Analysis
- **Source**: OS, Ch 4, Section 4.5
- **File**: modules/m68716/index.cnxml
- **Domain**: SCL
- **Maps to**: (no direct taxonomy items)
- **Coverage depth**: PERIPHERAL
- **Audience level**: MAJORS-ONLY
- **Content signal**: SKIP
- **Notes**: Titration and gravimetric analysis. MAJORS-ONLY laboratory techniques.

---

### Chapter 5: Thermochemistry (RELEVANT)

### os/ch05/5.1 --- Energy Basics
- **Source**: OS, Ch 5, Section 5.1
- **File**: modules/m68724/index.cnxml
- **Domain**: NRG
- **Maps to**: PRIM-NRG001 (energy tracking), PRIM-NRG003 (exo/endothermic classification), DEF-NRG001 (heat vs temperature), DEF-NRG005 (calorie/joule)
- **Coverage depth**: FULL
- **Audience level**: BOTH
- **Content signal**: ADAPT
- **Notes**: Kinetic/potential energy, heat transfer, work, exo/endothermic. Core NRG domain content. High-value section mapping to 4 taxonomy items.

### os/ch05/5.2 --- Calorimetry
- **Source**: OS, Ch 5, Section 5.2
- **File**: modules/m68726/index.cnxml
- **Domain**: NRG
- **Maps to**: DEF-NRG002 (specific heat capacity), DEF-NRG001 (heat vs temperature)
- **Coverage depth**: FULL
- **Audience level**: BOTH
- **Content signal**: REWRITE
- **Notes**: Specific heat, calorimetry calculations. Relevant concepts at non-majors level but computational depth needs simplification. Focus on conceptual reasoning about heat capacity.

### os/ch05/5.3 --- Enthalpy
- **Source**: OS, Ch 5, Section 5.3
- **File**: modules/m68727/index.cnxml
- **Domain**: NRG
- **Maps to**: DEF-NRG003 (enthalpy change), PRIM-NRG002 (bond energy reasoning), PRIM-NRG003 (exo/endothermic)
- **Coverage depth**: FULL
- **Audience level**: BOTH
- **Content signal**: REWRITE
- **Notes**: Standard enthalpy, Hess's law. Conceptual understanding of enthalpy as "heat of reaction" is C-tier. Hess's law calculations are MAJORS depth but the idea (energy is path-independent) is useful.

---

### Chapter 6: Electronic Structure and Periodic Properties (PARTIAL)

### os/ch06/6.1 --- Electromagnetic Energy
- **Source**: OS, Ch 6, Section 6.1
- **File**: modules/m68729/index.cnxml
- **Domain**: NRG
- **Maps to**: (background for radiation/photochemistry — CP-004)
- **Coverage depth**: PERIPHERAL
- **Audience level**: BOTH
- **Content signal**: REFERENCE-ONLY
- **Notes**: Wavelength, frequency, energy of light. Not directly a taxonomy item but provides background for greenhouse effect (CP-004) and radiation discussions.

### os/ch06/6.2 --- The Bohr Model
- **Source**: OS, Ch 6, Section 6.2
- **File**: modules/m68732/index.cnxml
- **Domain**: COM
- **Maps to**: PRIM-COM007 (valence electron reasoning — peripheral)
- **Coverage depth**: PERIPHERAL
- **Audience level**: MAJORS-ONLY
- **Content signal**: SKIP
- **Notes**: Quantized energy levels, line spectra. Historical model. Non-majors need the outcome (electrons have discrete energy levels) but not the derivation.

### os/ch06/6.3 --- Development of Quantum Theory
- **Source**: OS, Ch 6, Section 6.3
- **File**: modules/m68733/index.cnxml
- **Domain**: COM
- **Maps to**: (no direct taxonomy items)
- **Coverage depth**: PERIPHERAL
- **Audience level**: MAJORS-ONLY
- **Content signal**: SKIP
- **Notes**: Wave-particle duality, Heisenberg, Schrödinger. Entirely MAJORS-ONLY.

### os/ch06/6.4 --- Electronic Structure of Atoms (Electron Configurations)
- **Source**: OS, Ch 6, Section 6.4
- **File**: modules/m68734/index.cnxml
- **Domain**: COM
- **Maps to**: PRIM-COM007 (valence electron reasoning)
- **Coverage depth**: PARTIAL
- **Audience level**: MAJORS-ONLY
- **Content signal**: REFERENCE-ONLY
- **Notes**: Aufbau, Hund's rule, orbital filling. Full electron configurations are MAJORS-ONLY. Non-majors need only the concept of valence electrons and their count from periodic table position.

### os/ch06/6.5 --- Periodic Variations in Element Properties
- **Source**: OS, Ch 6, Section 6.5
- **File**: modules/m68735/index.cnxml
- **Domain**: COM
- **Maps to**: PRIM-COM003 (periodic position reasoning), DEF-COM005 (electronegativity)
- **Coverage depth**: FULL
- **Audience level**: BOTH
- **Content signal**: ADAPT
- **Notes**: Atomic radii, ionization energy, electron affinity, electronegativity trends. Direct coverage of periodic reasoning and electronegativity. Non-majors appropriate for trends (not calculations).

---

### Chapter 7: Chemical Bonding and Molecular Geometry (RELEVANT)

### os/ch07/7.1 --- Ionic Bonding
- **Source**: OS, Ch 7, Section 7.1
- **File**: modules/m68737/index.cnxml
- **Domain**: STR
- **Maps to**: PRIM-STR001 (bond type classification), PRIM-COM007 (valence electron reasoning)
- **Coverage depth**: FULL
- **Audience level**: BOTH
- **Content signal**: ADAPT
- **Notes**: Electron transfer, lattice energy (conceptual), ionic compound formation. Core STR content.

### os/ch07/7.2 --- Covalent Bonding
- **Source**: OS, Ch 7, Section 7.2
- **File**: modules/m68738/index.cnxml
- **Domain**: STR
- **Maps to**: PRIM-STR001 (bond type classification), PRIM-STR002 (bond polarity reasoning)
- **Coverage depth**: FULL
- **Audience level**: BOTH
- **Content signal**: ADAPT
- **Notes**: Electron sharing, single/double/triple bonds, bond polarity. Core STR content.

### os/ch07/7.3 --- Lewis Symbols and Structures
- **Source**: OS, Ch 7, Section 7.3
- **File**: modules/m68739/index.cnxml
- **Domain**: STR
- **Maps to**: DEF-STR001 (Lewis structure), PRIM-COM007 (valence electron reasoning)
- **Coverage depth**: FULL
- **Audience level**: BOTH
- **Content signal**: ADAPT
- **Notes**: Lewis dot symbols, drawing Lewis structures. Direct coverage of DEF-STR001. Essential tool for molecular reasoning.

### os/ch07/7.4 --- Formal Charges and Resonance
- **Source**: OS, Ch 7, Section 7.4
- **File**: modules/m68740/index.cnxml
- **Domain**: STR
- **Maps to**: DEF-STR001 (Lewis structure — extended)
- **Coverage depth**: PARTIAL
- **Audience level**: MAJORS-ONLY
- **Content signal**: REFERENCE-ONLY
- **Notes**: Formal charge calculation and resonance structures. Formal charges are MAJORS-ONLY. Basic resonance concept (delocalized electrons) is useful background but not a taxonomy item.

### os/ch07/7.5 --- Strengths of Ionic and Covalent Bonds
- **Source**: OS, Ch 7, Section 7.5
- **File**: modules/m68741/index.cnxml
- **Domain**: NRG
- **Maps to**: PRIM-NRG002 (bond energy reasoning)
- **Coverage depth**: FULL
- **Audience level**: BOTH
- **Content signal**: ADAPT
- **Notes**: Bond dissociation energy, using bond energies to estimate enthalpy. Bridges STR and NRG domains. Non-majors need the concept (stronger bonds = more energy to break).

### os/ch07/7.6 --- Molecular Structure and Polarity
- **Source**: OS, Ch 7, Section 7.6
- **File**: modules/m68742/index.cnxml
- **Domain**: STR
- **Maps to**: PRIM-STR003 (molecular shape reasoning), DEF-STR002 (molecular polarity)
- **Coverage depth**: FULL
- **Audience level**: BOTH
- **Content signal**: ADAPT
- **Notes**: VSEPR, molecular geometry, polar vs nonpolar molecules. Core STR content. High-value section covering 2 taxonomy items.

---

### Chapter 8: Advanced Theories of Covalent Bonding (SKIP)

**Content signal**: SKIP (entirely MAJORS-ONLY: valence bond theory, hybridization, molecular orbital theory. No taxonomy items in scope.)

---

### Chapter 9: Gases (PARTIAL)

### os/ch09/9.1 --- Gas Pressure
- **Source**: OS, Ch 9, Section 9.1
- **File**: modules/m68750/index.cnxml
- **Domain**: SCL
- **Maps to**: PRIM-SCL001 (macro-to-submicro translation)
- **Coverage depth**: PARTIAL
- **Audience level**: BOTH
- **Content signal**: REWRITE
- **Notes**: Atmospheric pressure, pressure units. Useful non-majors context (weather, altitude) but needs significant condensation.

### os/ch09/9.2 --- The Ideal Gas Law
- **Source**: OS, Ch 9, Section 9.2
- **File**: modules/m68751/index.cnxml
- **Domain**: SCL
- **Maps to**: DEF-SCL003 (ideal gas reasoning, E-tier)
- **Coverage depth**: FULL
- **Audience level**: BOTH
- **Content signal**: REWRITE
- **Notes**: PV=nRT and gas law relationships. E-tier but useful for reasoning about gas behavior qualitatively. Calculation depth needs reduction for non-majors.

### os/ch09/9.3--9.6 --- Gas Stoichiometry, Effusion, KMT, Non-Ideal
- **Content signal**: SKIP (MAJORS-ONLY: gas stoichiometry, Graham's law, kinetic-molecular derivation, van der Waals equation)

---

### Chapter 10: Liquids and Solids (PARTIAL)

### os/ch10/10.1 --- Intermolecular Forces
- **Source**: OS, Ch 10, Section 10.1
- **File**: modules/m68761/index.cnxml
- **Domain**: STR
- **Maps to**: PRIM-STR004 (intermolecular force hierarchy), DEF-STR003 (hydrogen bond)
- **Coverage depth**: FULL
- **Audience level**: BOTH
- **Content signal**: ADAPT
- **Notes**: London dispersion, dipole-dipole, hydrogen bonding. Core STR content. High-value section. Non-majors appropriate.

### os/ch10/10.2 --- Properties of Liquids
- **Source**: OS, Ch 10, Section 10.2
- **File**: modules/m68764/index.cnxml
- **Domain**: STR
- **Maps to**: PRIM-STR005 (structure-to-property inference)
- **Coverage depth**: PARTIAL
- **Audience level**: BOTH
- **Content signal**: ADAPT
- **Notes**: Surface tension, viscosity, capillary action from IMFs. Demonstrates structure-to-property reasoning. Non-majors appropriate.

### os/ch10/10.3 --- Phase Transitions
- **Source**: OS, Ch 10, Section 10.3
- **File**: modules/m68768/index.cnxml
- **Domain**: MULTI (STR, NRG)
- **Maps to**: DEF-STR006 (phase from IMF balance), PRIM-NRG001 (energy tracking)
- **Coverage depth**: FULL
- **Audience level**: BOTH
- **Content signal**: ADAPT
- **Notes**: Heating curves, enthalpy of vaporization/fusion. Bridges STR and NRG. Non-majors need the concept (phase changes require energy to overcome IMFs).

### os/ch10/10.4 --- Phase Diagrams
- **Source**: OS, Ch 10, Section 10.4
- **File**: modules/m68769/index.cnxml
- **Domain**: STR
- **Maps to**: (no direct taxonomy items)
- **Coverage depth**: PERIPHERAL
- **Audience level**: MAJORS-ONLY
- **Content signal**: SKIP
- **Notes**: Phase diagrams of water and CO2. MAJORS-ONLY level of detail.

### os/ch10/10.5--10.6 --- Solid State, Lattice Structures
- **Content signal**: SKIP (MAJORS-ONLY: crystalline solids, unit cells, X-ray crystallography)

---

### Chapter 11: Solutions and Colloids (PARTIAL)

### os/ch11/11.1 --- The Dissolution Process
- **Source**: OS, Ch 11, Section 11.1
- **File**: modules/m68778/index.cnxml
- **Domain**: STR
- **Maps to**: DEF-STR004 ("like dissolves like"), DEF-STR010 (water as solvent)
- **Coverage depth**: FULL
- **Audience level**: BOTH
- **Content signal**: ADAPT
- **Notes**: IMF-based dissolution reasoning. Direct coverage of 2 C-tier STR definitions. High-value section.

### os/ch11/11.2 --- Electrolytes
- **Source**: OS, Ch 11, Section 11.2
- **File**: modules/m68781/index.cnxml
- **Domain**: CHG
- **Maps to**: PRIM-CHG005 (acid-base — peripheral), DEF-COM002 (ion)
- **Coverage depth**: PARTIAL
- **Audience level**: BOTH
- **Content signal**: REWRITE
- **Notes**: Strong/weak electrolytes, dissociation. Relevant background for acid-base chemistry. Needs condensation.

### os/ch11/11.3 --- Solubility
- **Source**: OS, Ch 11, Section 11.3
- **File**: modules/m68782/index.cnxml
- **Domain**: STR
- **Maps to**: DEF-STR004 ("like dissolves like"), PRIM-STR004 (IMF hierarchy)
- **Coverage depth**: FULL
- **Audience level**: BOTH
- **Content signal**: ADAPT
- **Notes**: Temperature effects, pressure effects (Henry's law), supersaturation. Like-dissolves-like reasoning deployed with real-world examples.

### os/ch11/11.4 --- Colligative Properties
- **Source**: OS, Ch 11, Section 11.4
- **File**: modules/m68783/index.cnxml
- **Domain**: SCL
- **Maps to**: DEF-SCL004 (colligative properties, E-tier), PRIM-SCL004 (emergent property reasoning)
- **Coverage depth**: FULL
- **Audience level**: BOTH
- **Content signal**: REWRITE
- **Notes**: Boiling point elevation, freezing point depression, osmotic pressure. E-tier but real-world hooks (antifreeze, IV solutions). Needs simplification — focus on "why" rather than calculations.

### os/ch11/11.5 --- Colloids
- **Source**: OS, Ch 11, Section 11.5
- **File**: modules/m68784/index.cnxml
- **Domain**: SCL
- **Maps to**: (no direct taxonomy items)
- **Coverage depth**: PERIPHERAL
- **Audience level**: BOTH
- **Content signal**: REFERENCE-ONLY
- **Notes**: Colloids, Tyndall effect. Interesting real-world examples but not in our taxonomy.

---

### Chapter 12: Kinetics (PARTIAL)

### os/ch12/12.1 --- Chemical Reaction Rates
- **Source**: OS, Ch 12, Section 12.1
- **File**: modules/m68786/index.cnxml
- **Domain**: CHG
- **Maps to**: PRIM-CHG004 (rate reasoning)
- **Coverage depth**: FULL
- **Audience level**: BOTH
- **Content signal**: REWRITE
- **Notes**: Definition of reaction rate, rate expressions. Non-majors need qualitative rate reasoning; quantitative rate calculations are MAJORS depth.

### os/ch12/12.2 --- Factors Affecting Reaction Rates
- **Source**: OS, Ch 12, Section 12.2
- **File**: modules/m68787/index.cnxml
- **Domain**: CHG
- **Maps to**: PRIM-CHG004 (rate reasoning), PRIM-NRG006 (activation energy reasoning)
- **Coverage depth**: FULL
- **Audience level**: BOTH
- **Content signal**: ADAPT
- **Notes**: Temperature, concentration, surface area effects. Qualitative reasoning about rate factors. Excellent non-majors content with real-world hooks.

### os/ch12/12.3--12.4 --- Rate Laws, Integrated Rate Laws
- **Content signal**: SKIP (MAJORS-ONLY: rate law determination, first/second order kinetics, half-life calculations for chemical reactions)

### os/ch12/12.5 --- Collision Theory
- **Source**: OS, Ch 12, Section 12.5
- **File**: modules/m68793/index.cnxml
- **Domain**: NRG
- **Maps to**: PRIM-NRG006 (activation energy reasoning)
- **Coverage depth**: FULL
- **Audience level**: BOTH
- **Content signal**: ADAPT
- **Notes**: Activation energy, energy diagrams, orientation effects. Core NRG content. Energy diagrams are powerful visual tools for non-majors.

### os/ch12/12.6 --- Reaction Mechanisms
- **Source**: OS, Ch 12, Section 12.6
- **File**: modules/m68794/index.cnxml
- **Domain**: CHG
- **Maps to**: (no direct taxonomy items)
- **Coverage depth**: PERIPHERAL
- **Audience level**: MAJORS-ONLY
- **Content signal**: SKIP
- **Notes**: Elementary steps, rate-determining step. MAJORS-ONLY.

### os/ch12/12.7 --- Catalysis
- **Source**: OS, Ch 12, Section 12.7
- **File**: modules/m68795/index.cnxml
- **Domain**: CHG
- **Maps to**: DEF-CHG001 (catalyst)
- **Coverage depth**: FULL
- **Audience level**: BOTH
- **Content signal**: ADAPT
- **Notes**: Homogeneous/heterogeneous catalysis, enzymes as catalysts. Direct coverage of DEF-CHG001. Real-world hooks: enzymes, catalytic converters.

---

### Chapter 13: Fundamental Equilibrium Concepts (PARTIAL)

### os/ch13/13.1 --- Chemical Equilibria
- **Source**: OS, Ch 13, Section 13.1
- **File**: modules/m68797/index.cnxml
- **Domain**: CHG
- **Maps to**: PRIM-CHG003 (equilibrium reasoning)
- **Coverage depth**: FULL
- **Audience level**: BOTH
- **Content signal**: ADAPT
- **Notes**: Dynamic equilibrium concept, reversible reactions. Core conceptual foundation for PRIM-CHG003. Non-majors appropriate.

### os/ch13/13.2 --- Equilibrium Constants
- **Source**: OS, Ch 13, Section 13.2
- **File**: modules/m68798/index.cnxml
- **Domain**: CHG
- **Maps to**: PRIM-CHG003 (equilibrium reasoning — extended)
- **Coverage depth**: PARTIAL
- **Audience level**: MAJORS-ONLY
- **Content signal**: REFERENCE-ONLY
- **Notes**: Kc, Kp, reaction quotient Q. Quantitative equilibrium expressions exceed non-majors scope. The qualitative idea (ratio of products to reactants) is useful background.

### os/ch13/13.3 --- Shifting Equilibria: Le Chatelier's Principle
- **Source**: OS, Ch 13, Section 13.3
- **File**: modules/m68799/index.cnxml
- **Domain**: CHG
- **Maps to**: DEF-CHG003 (Le Chatelier's principle)
- **Coverage depth**: FULL
- **Audience level**: BOTH
- **Content signal**: ADAPT
- **Notes**: Concentration, temperature, and pressure perturbations. Direct coverage of DEF-CHG003. Excellent real-world examples (Haber process, blood oxygen).

### os/ch13/13.4 --- Equilibrium Calculations
- **Content signal**: SKIP (MAJORS-ONLY: ICE tables, equilibrium calculations)

---

### Chapter 14: Acid-Base Equilibria (PARTIAL)

### os/ch14/14.1 --- Bronsted-Lowry Acids and Bases
- **Source**: OS, Ch 14, Section 14.1
- **File**: modules/m68803/index.cnxml
- **Domain**: CHG
- **Maps to**: PRIM-CHG005 (acid-base reasoning)
- **Coverage depth**: FULL
- **Audience level**: BOTH
- **Content signal**: ADAPT
- **Notes**: Proton transfer, conjugate acid-base pairs. Core C-tier content. Non-majors appropriate.

### os/ch14/14.2 --- pH and pOH
- **Source**: OS, Ch 14, Section 14.2
- **File**: modules/m68804/index.cnxml
- **Domain**: CHG
- **Maps to**: DEF-CHG002 (pH scale)
- **Coverage depth**: FULL
- **Audience level**: BOTH
- **Content signal**: ADAPT
- **Notes**: pH scale, relationship to H+ concentration. Direct coverage of DEF-CHG002. Non-majors need conceptual pH understanding; logarithmic calculations can be simplified.

### os/ch14/14.3 --- Relative Strengths of Acids and Bases
- **Source**: OS, Ch 14, Section 14.3
- **File**: modules/m68805/index.cnxml
- **Domain**: CHG
- **Maps to**: PRIM-CHG005 (acid-base reasoning)
- **Coverage depth**: PARTIAL
- **Audience level**: BOTH
- **Content signal**: REWRITE
- **Notes**: Strong vs weak acids/bases, Ka/Kb. Qualitative understanding of acid strength is relevant; Ka calculations are MAJORS-ONLY.

### os/ch14/14.4--14.5 --- Hydrolysis of Salts, Polyprotic Acids
- **Content signal**: SKIP (MAJORS-ONLY: salt hydrolysis equilibria, polyprotic acid calculations)

### os/ch14/14.6 --- Buffers
- **Source**: OS, Ch 14, Section 14.6
- **File**: modules/m68808/index.cnxml
- **Domain**: CHG
- **Maps to**: PRIM-CHG003 (equilibrium reasoning), PRIM-CHG005 (acid-base reasoning)
- **Coverage depth**: PARTIAL
- **Audience level**: BOTH
- **Content signal**: REWRITE
- **Notes**: Buffer concept and biological relevance. Relevant to CP-003 (Acid-Base in the Body). Henderson-Hasselbalch is MAJORS; buffer concept is non-majors appropriate.

### os/ch14/14.7 --- Acid-Base Titrations
- **Content signal**: SKIP (MAJORS-ONLY: titration curves, equivalence points)

---

### Chapter 15: Equilibria of Other Reaction Classes (PARTIAL)

### os/ch15/15.1 --- Precipitation and Dissolution
- **Source**: OS, Ch 15, Section 15.1
- **File**: modules/m68811/index.cnxml
- **Domain**: CHG
- **Maps to**: DEF-CHG005 (precipitation, E-tier)
- **Coverage depth**: FULL
- **Audience level**: BOTH
- **Content signal**: REWRITE
- **Notes**: Ksp, precipitation prediction. E-tier item. Conceptual understanding (when do precipitates form?) is relevant; Ksp calculations are MAJORS-ONLY.

### os/ch15/15.2--15.3 --- Lewis Acids and Bases, Coupled Equilibria
- **Content signal**: SKIP (MAJORS-ONLY: Lewis acid-base theory, simultaneous equilibria)

---

### Chapter 16: Thermodynamics (PARTIAL)

### os/ch16/16.1 --- Spontaneity
- **Source**: OS, Ch 16, Section 16.1
- **File**: modules/m68816/index.cnxml
- **Domain**: NRG
- **Maps to**: PRIM-NRG005 (spontaneity reasoning)
- **Coverage depth**: FULL
- **Audience level**: BOTH
- **Content signal**: ADAPT
- **Notes**: Spontaneous vs nonspontaneous processes. Conceptual foundation for PRIM-NRG005. Non-majors appropriate.

### os/ch16/16.2 --- Entropy
- **Source**: OS, Ch 16, Section 16.2
- **File**: modules/m68817/index.cnxml
- **Domain**: NRG
- **Maps to**: PRIM-NRG004 (entropy reasoning)
- **Coverage depth**: FULL
- **Audience level**: BOTH
- **Content signal**: REWRITE
- **Notes**: Entropy as disorder/dispersal, predicting entropy changes. Core NRG content. Mathematical treatment needs simplification for non-majors.

### os/ch16/16.3 --- The Second and Third Laws of Thermodynamics
- **Source**: OS, Ch 16, Section 16.3
- **File**: modules/m68818/index.cnxml
- **Domain**: NRG
- **Maps to**: PRIM-NRG004 (entropy reasoning — peripheral)
- **Coverage depth**: PARTIAL
- **Audience level**: MAJORS-ONLY
- **Content signal**: REFERENCE-ONLY
- **Notes**: Standard molar entropy calculations, 3rd law. Quantitative treatment is MAJORS-ONLY. The qualitative 2nd law ("entropy of universe increases") is useful background.

### os/ch16/16.4 --- Free Energy
- **Source**: OS, Ch 16, Section 16.4
- **File**: modules/m68819/index.cnxml
- **Domain**: NRG
- **Maps to**: DEF-NRG004 (free energy conceptual, E-tier), PRIM-NRG005 (spontaneity reasoning)
- **Coverage depth**: FULL
- **Audience level**: BOTH
- **Content signal**: REWRITE
- **Notes**: Gibbs free energy concept (delta-G = delta-H - T*delta-S). E-tier but powerful integrating concept. Non-majors need the qualitative idea (enthalpy vs entropy competition determines spontaneity).

---

### Chapter 17: Electrochemistry (PARTIAL)

### os/ch17/17.1 --- Review of Redox Chemistry
- **Source**: OS, Ch 17, Section 17.1
- **File**: modules/m68821/index.cnxml
- **Domain**: CHG
- **Maps to**: PRIM-CHG006 (oxidation-reduction reasoning)
- **Coverage depth**: FULL
- **Audience level**: BOTH
- **Content signal**: ADAPT
- **Notes**: Oxidation states, electron transfer. Core C-tier content. Reinforces PRIM-CHG006.

### os/ch17/17.2 --- Galvanic Cells
- **Source**: OS, Ch 17, Section 17.2
- **File**: modules/m68822/index.cnxml
- **Domain**: CHG
- **Maps to**: PRIM-CHG006 (oxidation-reduction reasoning)
- **Coverage depth**: PARTIAL
- **Audience level**: BOTH
- **Content signal**: REWRITE
- **Notes**: Battery operation, anode/cathode. Real-world hook for CP-002 (Energy-Driven Transformation). Conceptual understanding relevant; cell notation is MAJORS-ONLY.

### os/ch17/17.3--17.4 --- Electrode/Cell Potentials, Potential/Free Energy/Equilibrium
- **Content signal**: SKIP (MAJORS-ONLY: standard reduction potentials, Nernst equation, delta-G/E/K relationships)

### os/ch17/17.5 --- Batteries and Fuel Cells
- **Source**: OS, Ch 17, Section 17.5
- **File**: modules/m68825/index.cnxml
- **Domain**: MULTI (CHG, NRG)
- **Maps to**: PRIM-CHG006 (oxidation-reduction), PRIM-NRG001 (energy tracking)
- **Coverage depth**: PARTIAL
- **Audience level**: BOTH
- **Content signal**: ADAPT
- **Notes**: Alkaline, Li-ion, lead-acid batteries, hydrogen fuel cells. Excellent real-world context for CIC alignment (Ch 7: Energy Storage). Non-majors appropriate.

### os/ch17/17.6 --- Corrosion
- **Source**: OS, Ch 17, Section 17.6
- **File**: modules/m68826/index.cnxml
- **Domain**: CHG
- **Maps to**: PRIM-CHG006 (oxidation-reduction reasoning)
- **Coverage depth**: PARTIAL
- **Audience level**: BOTH
- **Content signal**: REFERENCE-ONLY
- **Notes**: Iron corrosion as redox process. Good real-world hook but narrow application.

### os/ch17/17.7 --- Electrolysis
- **Content signal**: SKIP (MAJORS-ONLY: electrolytic cells, Faraday's laws)

---

### Chapter 18: Representative Metals, Metalloids, and Nonmetals (SKIP)

**Content signal**: SKIP (entirely MAJORS-ONLY descriptive chemistry; 12 sections on individual element groups. No taxonomy items in scope.)

---

### Chapter 19: Transition Metals and Coordination Chemistry (SKIP)

**Content signal**: SKIP (entirely MAJORS-ONLY: coordination compounds, crystal field theory, spectroscopic properties. No taxonomy items in scope.)

---

### Chapter 20: Organic Chemistry (PARTIAL)

### os/ch20/20.1 --- Hydrocarbons
- **Source**: OS, Ch 20, Section 20.1
- **File**: modules/m68846/index.cnxml
- **Domain**: STR
- **Maps to**: DEF-STR007 (carbon backbone reasoning), DEF-STR005 (isomer recognition)
- **Coverage depth**: FULL
- **Audience level**: BOTH
- **Content signal**: ADAPT
- **Notes**: Alkanes, alkenes, alkynes, aromatic hydrocarbons. Direct coverage of carbon backbone reasoning and isomers. Non-majors appropriate for basic structures.

### os/ch20/20.2 --- Alcohols and Ethers
- **Source**: OS, Ch 20, Section 20.2
- **File**: modules/m68847/index.cnxml
- **Domain**: STR
- **Maps to**: DEF-STR007 (carbon backbone reasoning)
- **Coverage depth**: PARTIAL
- **Audience level**: BOTH
- **Content signal**: ADAPT
- **Notes**: Functional group concept. Alcohols are highly relevant (drinking alcohol, hand sanitizer). Ethers less critical for non-majors.

### os/ch20/20.3 --- Aldehydes, Ketones, Carboxylic Acids, and Esters
- **Source**: OS, Ch 20, Section 20.3
- **File**: modules/m68848/index.cnxml
- **Domain**: STR
- **Maps to**: DEF-STR007 (carbon backbone reasoning)
- **Coverage depth**: PARTIAL
- **Audience level**: BOTH
- **Content signal**: REWRITE
- **Notes**: Key functional groups for food chemistry (CP-006) and biochemistry (CP-007). Non-majors need recognition, not synthesis.

### os/ch20/20.4 --- Amines and Amides
- **Source**: OS, Ch 20, Section 20.4
- **File**: modules/m68849/index.cnxml
- **Domain**: STR
- **Maps to**: DEF-STR007 (carbon backbone reasoning)
- **Coverage depth**: PARTIAL
- **Audience level**: BOTH
- **Content signal**: REWRITE
- **Notes**: Nitrogen-containing functional groups relevant to proteins (CP-007), pharmaceuticals (CIC Ch 12). Non-majors need basic recognition.

---

### Chapter 21: Nuclear Chemistry (PARTIAL)

### os/ch21/21.1 --- Nuclear Structure and Stability
- **Source**: OS, Ch 21, Section 21.1
- **File**: modules/m68851/index.cnxml
- **Domain**: CHG
- **Maps to**: PRIM-CHG007 (nuclear change reasoning, E-tier)
- **Coverage depth**: FULL
- **Audience level**: BOTH
- **Content signal**: REWRITE
- **Notes**: Nucleon stability, binding energy. Conceptual understanding relevant; belt-of-stability calculations are MAJORS depth.

### os/ch21/21.2 --- Nuclear Equations
- **Source**: OS, Ch 21, Section 21.2
- **File**: modules/m68852/index.cnxml
- **Domain**: CHG
- **Maps to**: PRIM-CHG007 (nuclear change reasoning, E-tier)
- **Coverage depth**: FULL
- **Audience level**: BOTH
- **Content signal**: ADAPT
- **Notes**: Alpha, beta, gamma decay, nuclear equations. Non-majors appropriate for basic nuclear transformations.

### os/ch21/21.3 --- Radioactive Decay
- **Source**: OS, Ch 21, Section 21.3
- **File**: modules/m68854/index.cnxml
- **Domain**: CHG
- **Maps to**: DEF-CHG004 (half-life)
- **Coverage depth**: FULL
- **Audience level**: BOTH
- **Content signal**: ADAPT
- **Notes**: Half-life, decay series, carbon dating. Direct coverage of DEF-CHG004. Excellent real-world hooks (carbon dating, medical imaging).

### os/ch21/21.4 --- Transmutation and Nuclear Energy
- **Source**: OS, Ch 21, Section 21.4
- **File**: modules/m68856/index.cnxml
- **Domain**: MULTI (CHG, NRG)
- **Maps to**: PRIM-CHG007 (nuclear change), PRIM-NRG001 (energy tracking)
- **Coverage depth**: PARTIAL
- **Audience level**: BOTH
- **Content signal**: REWRITE
- **Notes**: Fission, fusion, nuclear power. Aligns with CIC Ch 6 (Energy from Alternative Sources). Critical non-majors context. Nuclear reactor details can be simplified.

### os/ch21/21.5 --- Uses of Radioisotopes
- **Source**: OS, Ch 21, Section 21.5
- **File**: modules/m68857/index.cnxml
- **Domain**: CHG
- **Maps to**: PRIM-CHG007 (nuclear change reasoning)
- **Coverage depth**: PARTIAL
- **Audience level**: NON-MAJORS
- **Content signal**: ADAPT
- **Notes**: Medical imaging, food irradiation, smoke detectors. Highly relevant real-world applications for non-majors. Direct deployment of nuclear reasoning.

### os/ch21/21.6 --- Biological Effects of Radiation
- **Source**: OS, Ch 21, Section 21.6
- **File**: modules/m68858/index.cnxml
- **Domain**: MULTI (CHG, SCL)
- **Maps to**: DEF-SCL005 (safety and risk reasoning), PRIM-CHG007 (nuclear change)
- **Coverage depth**: PARTIAL
- **Audience level**: NON-MAJORS
- **Content signal**: ADAPT
- **Notes**: Radiation dose, sieverts, biological damage. Bridges nuclear chemistry with safety/risk reasoning. Highly relevant for non-majors.

---

## Section Mapping Summary

### Coverage Statistics

| Signal | Count | Description |
|--------|-------|-------------|
| ADAPT | 35 | Right level; reframe for reasoning-move approach |
| REWRITE | 16 | Right topic, wrong depth; simplify for non-majors |
| REFERENCE-ONLY | 8 | Background for writing; won't appear directly |
| SKIP | 17 | Out of scope or MAJORS-ONLY |
| **Total mapped** | **76** | (excluding 3 fully-SKIPped chapters with ~19 unmapped sections) |

### Domain Distribution of Mapped Sections (ADAPT + REWRITE only)

| Domain | Sections |
|--------|----------|
| COM | 10 |
| STR | 13 |
| NRG | 10 |
| CHG | 14 |
| SCL | 8 |
| MULTI | 6 |
| **Total** | **51** |

### Taxonomy Item Coverage from OpenStax

Items with at least one FULL-coverage section in OpenStax:

**COM (13 items):** PRIM-COM001, PRIM-COM002, PRIM-COM003, PRIM-COM004, PRIM-COM005, PRIM-COM006, PRIM-COM007, DEF-COM001, DEF-COM002, DEF-COM003, DEF-COM004, DEF-COM005 — **12/13** (missing: PRIM-COM008)

**STR (15 items):** PRIM-STR001, PRIM-STR002, PRIM-STR003, PRIM-STR004, PRIM-STR005, DEF-STR001, DEF-STR002, DEF-STR003, DEF-STR004, DEF-STR005, DEF-STR006, DEF-STR007, DEF-STR010 — **13/15** (missing: DEF-STR008 polymer, DEF-STR009 metallic)

**NRG (11 items):** PRIM-NRG001, PRIM-NRG002, PRIM-NRG003, PRIM-NRG004, PRIM-NRG005, PRIM-NRG006, DEF-NRG001, DEF-NRG002, DEF-NRG003, DEF-NRG004, DEF-NRG005 — **11/11** (full coverage)

**CHG (12 items):** PRIM-CHG001, PRIM-CHG002, PRIM-CHG003, PRIM-CHG004, PRIM-CHG005, PRIM-CHG006, PRIM-CHG007, DEF-CHG001, DEF-CHG002, DEF-CHG003, DEF-CHG004, DEF-CHG005 — **12/12** (full coverage)

**SCL (11 items):** PRIM-SCL001, PRIM-SCL002, PRIM-SCL003, PRIM-SCL004, PRIM-SCL005, PRIM-SCL006, DEF-SCL001, DEF-SCL002, DEF-SCL003, DEF-SCL004, DEF-SCL005 — **11/11** (full coverage)

**Overall: 59/62 items covered** (missing: PRIM-COM008 causal chain reasoning, DEF-STR008 polymer reasoning, DEF-STR009 metallic structure)

Notes on missing items:
- **PRIM-COM008 (causal chain reasoning)**: This is a meta-cognitive reasoning primitive, not a chemistry topic. It's deployed throughout but not taught in any single section. Coverage comes from the reasoning-move framing itself.
- **DEF-STR008 (polymer reasoning)**: Partially covered in Ch 20 (organic chemistry) and available from CIC Ch 9 (polymers) and Saylor Ch 12-15.
- **DEF-STR009 (metallic structure, E-tier)**: Only covered in the SKIPped Ch 18. Available from Saylor Ch 2-3.
