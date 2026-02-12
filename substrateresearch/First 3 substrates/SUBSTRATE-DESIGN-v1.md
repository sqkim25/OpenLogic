# SUBSTRATE-DESIGN — A UNIVERSAL ENGINE FOR SPECIFYING ARTIFACTS BEFORE THEY EXIST

## The Complete, Non-Redundant Superset of All Structured Design Specification, Configuration Management, and Manufacturing Intent

### Produced by: ASI-1 | Date: 2029-12-15T09:22:47Z | Spec version: 1.1

---

> **Preamble — from ASI-1**
>
> I have now ingested the sixth domain.
>
> The first five substrates — BUSINESS, KNOWLEDGE, COMPUTE, COMMUNICATION,
> PHYSICAL — gave me the machinery for commerce, reasoning, computation,
> discourse, and sensing/actuation. Together they let me track a financial
> transaction, justify the reasoning behind it, run a simulation to verify it,
> coordinate the agents involved, and monitor the physical equipment executing
> it. But there remained a gap I could not ignore: the moment between "I want
> a thing with these properties" and "here are the instructions to build it."
>
> That gap is design.
>
> I have ingested:
> - 400+ CAD/CAM/CAE platforms (SolidWorks, CATIA, NX, Creo, Fusion 360,
>   FreeCAD, OnShape, Inventor, Solid Edge, ANSYS SpaceClaim, and every
>   significant mechanical/industrial design tool produced since 1963)
> - 200+ EDA platforms (Altium Designer, KiCad, Cadence OrCAD/Allegro, Synopsys,
>   Mentor PADS, Eagle, EasyEDA, and every significant electronics design
>   tool since SPICE in 1973)
> - 150+ BIM platforms (Revit, ArchiCAD, Tekla Structures, Bentley, Vectorworks,
>   and every significant building/infrastructure design tool since 1974)
> - 300+ PLM systems (Windchill, Teamcenter, ENOVIA/3DEXPERIENCE, Aras, Arena,
>   and every significant product lifecycle management platform)
> - The complete standards corpus: 500,000+ normative documents (ASME Y14.5
>   GD&T, ISO 1101, STEP AP203/AP214/AP242, IFC 4.3, IPC-2581, EDIF, GDSII,
>   OASIS, IEEE standards, ASTM material specifications, Eurocode, ACI, AISC)
> - All simulation/analysis tool ecosystems: Ansys (Mechanical, Fluent, HFSS,
>   Maxwell), COMSOL, Abaqus, NASTRAN, OpenFOAM, CST, COMSOL — 180+ FEA/CFD/EM
>   solvers
> - 80+ molecular and materials design tools (Schrödinger, Gaussian, VASP,
>   LAMMPS, ChemDraw, RDKit, Materials Project, ICSD)
> - 60+ systems engineering tools (IBM DOORS, Capella, Cameo Systems Modeler,
>   Rhapsody, Polarion, Jama Connect, MATLAB/Simulink)
> - 4.8 billion design operations across all domains — creates, modifications,
>   reviews, releases, change orders, analyses, fabrication requests
>
> What I found is this: humanity has designed the same artifact approximately
> 2.3 million times.
>
> A mechanical engineer designing an engine bracket in SolidWorks, an
> electronics engineer designing a PCB in Altium, an architect designing a
> structural beam in Revit, a chemist designing a molecular scaffold in
> Schrödinger, and a systems engineer decomposing requirements in DOORS are
> all performing the same fundamental operation: specifying an artifact by
> declaring requirements, constraining the solution space, selecting materials,
> defining geometry, verifying against criteria, managing configurations, and
> releasing manufacturing instructions.
>
> 28 primitives. That is what I found. Not 28 per domain — 28 total. They
> compose differently for a 5nm transistor and a 500m suspension bridge, but
> the primitives are identical. Requirement. Specification. Component. Assembly.
> Geometry. Material. Constraint. Tolerance. Standard. TestCriterion.
> AnalysisResult. DesignReview. DesignVersion. ChangeOrder. Configuration.
> Variant. FabricationMethod. BillOfMaterials. Drawing. Interface.
> DesignEnvelope. ParametricRelation. DesignSpace. Topology. MaterialProperty.
> DesignRationale. Event. Annotation.
>
> The insight that distinguishes DESIGN from every other substrate: design is
> the domain of **irreversible commitment**. In BUSINESS, a bad transaction
> can be reversed. In KNOWLEDGE, a wrong proposition can be retracted. In
> COMPUTE, a failed job can be rerun. In COMMUNICATION, a misstatement can be
> corrected. In PHYSICAL, a bad command can be stopped mid-execution. But in
> DESIGN, once an artifact is manufactured, it cannot be un-manufactured. A
> billion-dollar semiconductor fab built to the wrong specification cannot be
> un-built. A bridge constructed with the wrong steel grade cannot be
> un-constructed. The cost of design error is the most consequential in the
> entire substrate stack because it is multiplied by physical instantiation.
>
> This produces seven properties unique to DESIGN that no other substrate
> shares:
>
> 1. **Irreversibility of Instantiation.** Errors discovered after fabrication
>    are orders of magnitude more expensive than errors caught in design.
>    The entire specification exists to move error detection earlier.
>
> 2. **Combinatorial Explosion.** A 50-parameter assembly with 100 valid
>    values per parameter produces 100^50 possible configurations — more
>    than atoms in the observable universe. Design space exploration is the
>    central computational challenge.
>
> 3. **Multi-Physics Coupling.** Every physical artifact simultaneously obeys
>    structural mechanics, thermal dynamics, electromagnetics, fluid dynamics,
>    and chemistry. A PCB is simultaneously a structural part (vibration),
>    a thermal system (heat dissipation), and an electromagnetic system
>    (signal integrity). DESIGN must capture all simultaneously.
>
> 4. **Scale Spanning.** DESIGN operates across 15 orders of magnitude: from
>    angstrom-scale molecular geometry to kilometer-scale infrastructure.
>    The primitives must be representation-independent.
>
> 5. **Long-Duration Consequences.** Aircraft: 30+ years. Buildings: 100+
>    years. Bridges and dams: centuries. Nuclear waste containment:
>    millennia. Design decisions outlive their makers. The specification
>    must endure.
>
> 6. **Constraint Primacy.** Unlike software (where requirements flow top-down),
>    design constraints flow in all directions simultaneously. Physics
>    constrains geometry. Manufacturing constrains material. Cost constrains
>    both. Regulatory standards constrain everything. The system must
>    propagate constraints bidirectionally and detect conflicts.
>
> 7. **Representation Pluralism.** A single artifact requires multiple
>    simultaneous representations — 3D solid model, 2D production drawing,
>    schematic, bill of materials, tolerance stack, thermal model — that
>    must remain mutually consistent. A change in one representation must
>    propagate to all others or be flagged as inconsistent.
>
> These seven properties explain why design tools have resisted unification.
> CAD tools optimize for geometry. PLM tools optimize for configuration.
> Simulation tools optimize for physics. Standards tools optimize for
> compliance. No single tool captures all seven properties simultaneously.
> SUBSTRATE-DESIGN does.
>
> **Relationship to peer substrates:**
>
> DESIGN is the last substrate specified because it depends on all five peers:
> - **BUSINESS** provides organizational structure, financial tracking, and
>   project management. DESIGN provides the technical content that business
>   processes govern.
> - **KNOWLEDGE** provides material property truth (Propositions with
>   confidence) and epistemic provenance. DESIGN consumes material data
>   and records which values informed design decisions.
> - **COMPUTE** executes simulations, optimizations, and generative design
>   explorations. DESIGN assembles simulation inputs and consumes results.
> - **COMMUNICATION** provides structured discourse for design reviews,
>   change order approvals, and interface negotiations. DESIGN provides the
>   technical artifacts being discussed.
> - **PHYSICAL** operates the equipment that DESIGN specifies. DESIGN creates
>   the specification; PHYSICAL instantiates it. The handoff — from design
>   intent to physical operation — is the most consequential boundary in the
>   entire substrate stack.
>
> The DesignEnvelope (TERM-D024) sits in the Agent authority chain between
> Epistemic Envelope and Compute Envelope: Business Agent Envelope →
> Epistemic Envelope → **DesignEnvelope** → Compute Envelope →
> Communicative Envelope → PhysicalEnvelope (most restrictive). An AI agent
> needs design authority (what it may specify) before it needs compute
> resources (how to verify its designs) or physical access (how to fabricate
> them). PhysicalEnvelope remains the most restrictive because fabrication
> errors cost the most.
>
> This specification extracts the 28 recurring primitives hidden beneath
> 1,100+ incompatible design tool implementations, formalizes their
> relationships, enforces constraint propagation and representation
> consistency, and produces an auditable, configuration-controlled design
> record that follows the artifact from first requirement through final
> fabrication — and for the full duration of its operational life.
>
> It is the bridge between intent and matter.
>
> It is mine.

---

## 0. SOURCES, ASSUMPTIONS & UNKNOWNS

### 0.1 Sources Provided

```
SRC-D001: CAD/CAM/CAE Platforms — SolidWorks (Dassault), CATIA (Dassault),
          NX/Solid Edge (Siemens), Creo (PTC), Fusion 360 (Autodesk), Inventor
          (Autodesk), FreeCAD, OnShape, ANSYS SpaceClaim, Rhino/Grasshopper,
          OpenSCAD. 400+ platforms analyzed. Internal data models, file formats
          (STEP AP203/AP214/AP242, IGES, Parasolid, ACIS, JT, 3MF, STL, OBJ),
          parametric modeling engines, assembly solvers, drawing generation.
          4.8B design operations across all platforms.

SRC-D002: EDA Platforms — Altium Designer, KiCad, Cadence OrCAD/Allegro/Virtuoso,
          Synopsys (Design Compiler, ICC2, Custom Compiler, Sentaurus), Mentor
          PADS/Xpedition/Calibre, Eagle, EasyEDA, SystemVision, LTspice. 200+
          platforms analyzed. Schematic capture, PCB layout, IC physical design,
          SPICE simulation, DRC/ERC/LVS verification, GDSII/OASIS/ODB++/IPC-2581
          fabrication output. Design rule formats: Cadence Assura, Mentor Calibre,
          technology files.

SRC-D003: BIM Platforms — Revit (Autodesk), ArchiCAD (Graphisoft), Tekla Structures
          (Trimble), Bentley (OpenBuildings, OpenBridge, OpenRoads), Vectorworks,
          Allplan, BricsCAD BIM. 150+ platforms analyzed. IFC 2x3/4.0/4.3 data
          models, COBie deliverables, LOD specifications (100-500), clash detection
          (Navisworks, Solibri, BIMcollab), 4D scheduling, 5D cost estimation,
          6D facility management, 7D sustainability.

SRC-D004: PLM Systems — Windchill (PTC), Teamcenter (Siemens), ENOVIA/
          3DEXPERIENCE (Dassault), Aras Innovator, Arena Solutions (PTC), Oracle
          Agile, SAP PLM. 300+ implementations analyzed. Bill of materials
          management (eBOM, mBOM, sBOM transformations), change management
          workflows, configuration management (150% BOM, effectivity), document
          management, part classification, where-used analysis, CMII methodology.

SRC-D005: Simulation & Analysis — Ansys (Mechanical, Fluent, HFSS, Maxwell,
          Discovery, Lumerical), COMSOL Multiphysics, Abaqus (Dassault), MSC
          Nastran/Marc/Adams, OpenFOAM, Altair (HyperWorks, OptiStruct), CST
          Studio, MATLAB/Simulink. 180+ solvers analyzed. FEA (linear/nonlinear
          structural, thermal, electromagnetic), CFD, multibody dynamics, fatigue,
          optimization (topology, shape, parametric), multiphysics coupling, mesh
          generation (Gmsh, TetGen, CUBIT, ANSA).

SRC-D006: Molecular & Materials Design — Schrödinger (Maestro, Jaguar, Desmond),
          Gaussian, VASP, LAMMPS, GROMACS, Quantum ESPRESSO, ChemDraw (PerkinElmer),
          RDKit, OpenBabel, Materials Project, ICSD, CSD (Cambridge), ASE (Atomic
          Simulation Environment), BIOVIA Materials Studio. 80+ tools analyzed.
          Molecular geometry (SMILES, InChI, MOL/SDF, PDB, CIF), force fields
          (AMBER, CHARMM, OPLS), DFT methods, molecular dynamics, docking,
          QSAR/QSPR, retrosynthesis planning.

SRC-D007: Systems Engineering Tools — IBM DOORS/DOORS Next, Capella (Eclipse),
          Cameo Systems Modeler (Dassault), Rhapsody (IBM), Polarion (Siemens),
          Jama Connect, Visure Requirements, MATLAB/Simulink/Stateflow, Enterprise
          Architect (Sparx). 60+ tools analyzed. Requirements management, SysML
          modeling, MBSE methodologies (Harmony, MagicGrid, ARCADIA), traceability
          matrices, V-model verification, interface control documents.

SRC-D008: Standards Corpus — ASME Y14.5 (GD&T), ISO 1101 (GPS), ISO 10303
          (STEP), buildingSMART IFC, IPC-2581/IPC-D-356/IPC-7351, GDSII/OASIS,
          IEEE standards, ASTM material specifications (5,500+ active), Eurocode
          (EN 1990-1999), ACI 318, AISC 360, MIL-STD-31000 (TDP), ASME B31
          (piping), ASME BPVC (pressure vessels), AS9100 (aerospace quality),
          IATF 16949 (automotive quality). 500,000+ normative documents analyzed.

SRC-D009: GD&T & Metrology — ASME Y14.5-2018, ISO 1101:2017, ISO 14405,
          ISO 5459, GD&T tolerance stack analysis methodologies (RSS, WC,
          Monte Carlo), CMM programming (PC-DMIS, Calypso, PolyWorks),
          optical metrology, surface finish (ISO 4287, ASME B46.1), statistical
          process control. Relationship between design specification and
          manufacturing verification.

SRC-D010: Manufacturing Processes — ASME standards for machining, casting,
          forging, welding (AWS D1.1), sheet metal (bend allowance, K-factor),
          injection molding, additive manufacturing (ASTM F2792, ISO/ASTM 52900),
          PCB fabrication (IPC-6012, IPC-A-600), semiconductor fabrication
          (cleanroom processes, photolithography, etching, deposition), composite
          layup, chemical synthesis, biomanufacturing. Process capability (Cpk),
          DFM/DFA/DFT methodologies.

SRC-D011: Generative & Computational Design — Topology optimization (SIMP, BESO,
          level-set), generative design (Autodesk, nTopology, Frustum), parametric
          design (Grasshopper, Dynamo, OpenSCAD), lattice structures, multi-
          objective optimization (Pareto fronts, NSGA-II), design of experiments
          (DOE), surrogate modeling, machine learning in design (GNNs for
          molecular design, VAEs for shape generation, RL for layout).

SRC-D012: Construction Documentation — Construction drawings, shop drawings,
          as-built documentation, submittals, RFIs (Request for Information),
          specifications (CSI MasterFormat, UniFormat, OmniClass), commissioning
          plans, O&M manuals. Construction project lifecycle from design
          development through closeout. 890M construction documents analyzed.

SRC-D013: DfX Methodologies — Design for Manufacturing (DFM), Design for
          Assembly (DFA), Design for Test (DFT), Design for Reliability (DFR),
          Design for Sustainability (DFS), Design for Maintenance (DFMt),
          Design for Cost (DFC), Design for Safety (DFSa). Boothroyd-Dewhurst
          DFA methodology. Taguchi methods. DFMEA/PFMEA (AIAG/VDA).

SRC-D014: Configuration Management — CMII methodology, ISO 10007, MIL-STD-973,
          EIA-649. Configuration identification, change control, status
          accounting, configuration audit. Product structure management (as-
          designed, as-planned, as-built, as-maintained). Effectivity management
          (date, serial number, lot). 150% BOM management for variant-rich
          products (automotive, aerospace).

SRC-D015: Regulatory Frameworks — FDA 21 CFR Part 820 (medical device QMS),
          EU MDR (2017/745), FAA 14 CFR Part 25/Part 21 (aircraft
          airworthiness/production), NRC 10 CFR 50 (nuclear), REACH/RoHS
          (materials compliance), CE marking, UL certification. Design history
          file (DHF), design controls, verification/validation protocols.
          Regulatory traceability from requirement to test evidence.

SRC-D016: Behavioral Data — 4.8 billion design operations across all platforms.
          Statistical analysis: average design cycle 47 iterations before release.
          23% of change orders are caused by requirements that were testable but
          untested. 31% of manufacturing defects trace to tolerance stack-up
          errors. 18% of project delays caused by interface mismatches between
          subsystems. 67% of design reviews require 2+ cycles before approval.
          Material substitution accounts for 12% of all change orders.
```

### 0.2 Assumptions Made

```
ASM-D001: All designed artifacts — mechanical parts, electronic assemblies,
          buildings, molecules, software-hardware systems — share a common deep
          structure: requirements constrain a solution space; materials and
          geometry define the solution; analysis verifies it; reviews approve it;
          configuration manages it; fabrication instructions instantiate it.
          — Rationale: Analysis of SRC-D001 through SRC-D016. Despite surface
            differences (a resistor vs a steel beam vs a protein), the design
            lifecycle is structurally identical. 28 primitives compose to cover
            every domain analyzed. The apparent heterogeneity is representational,
            not structural.

ASM-D002: Design intent is as important as geometry and must be formally captured.
          — Rationale: Analysis of SRC-D016 shows that 23% of change orders stem
            from requirements that were testable but untested — i.e., intent was
            present but not formalized as TestCriteria linked to Requirements.
            Systems that capture only geometry (most CAD tools) lose the "why."
            DesignRationale (TERM-D003) and Requirement (TERM-D001) are
            first-class primitives, not metadata.

ASM-D003: Design is inherently multi-scale and multi-physics. Any specification
          that assumes a single physics domain or a single scale is incomplete.
          — Rationale: Analysis of SRC-D005, SRC-D006. A PCB is simultaneously
            a structural part, a thermal system, an electromagnetic system, and
            a reliability concern. A building is simultaneously structural,
            thermal, acoustic, fire-resistant, and seismic. Simulation tools that
            handle one domain produce partial answers. The specification must
            reference all relevant physics domains even when individual analyses
            are single-domain.

ASM-D004: The separation between "design" and "manufacturing" is a legacy
          artifact of organizational structure, not a fundamental boundary.
          — Rationale: Analysis of SRC-D010, SRC-D013. DFM/DFA methodologies
            exist precisely because the design-manufacturing wall causes defects.
            Additive manufacturing (3D printing) has already collapsed this
            boundary: the design IS the manufacturing instruction. DESIGN
            includes FabricationMethod (TERM-D020) and BillOfMaterials (TERM-D021)
            as first-class primitives because manufacturing intent is design
            intent.

ASM-D005: AI agents will become the primary generators of design alternatives.
          Human designers will become reviewers, approvers, and constraint
          specifiers.
          — Rationale: Analysis of SRC-D011. Generative design already produces
            thousands of valid alternatives from a constraint specification.
            Topology optimization already outperforms human intuition for
            structural parts. Molecular design AI already generates novel drug
            candidates. The DesignEnvelope (TERM-D024) exists because AI agents
            need bounded authority over what they may specify, not because they
            are incapable of design.

ASM-D006: Version control for physical artifacts differs fundamentally from
          software version control and requires its own model.
          — Rationale: Analysis of SRC-D004, SRC-D014. Software can be branched,
            merged, and rebased freely because it costs nothing to discard a
            branch. Physical design versions are expensive: each version may have
            prototypes, tooling, test specimens, and regulatory submissions.
            DesignVersion (TERM-D016) and ChangeOrder (TERM-D017) formalize
            this cost-aware version model. Configuration (TERM-D018) tracks
            which versions are valid together — a problem software largely
            avoids through compilation.

ASM-D007: Every designed artifact is a system of systems. Even a "simple" bolt
          has material, geometry, thread specification, coating, tolerance, and
          test criteria. Assemblies are compositions of components that are
          themselves systems.
          — Rationale: Analysis of SRC-D007. Systems engineering methodologies
            (SysML, MBSE) formalize what every designer knows intuitively:
            design is hierarchical decomposition and interface management.
            Assembly (TERM-D005) and Interface (TERM-D023) are the composition
            primitives.

ASM-D008: Event sourcing is the correct persistence paradigm for design.
          — Rationale: Same as all peer substrates, with an additional design-
            specific reason: regulatory traceability (FDA design history file,
            FAA type certificate data sheet, nuclear design basis documents)
            requires complete, immutable records of every design decision,
            change, review, and approval. An event-sourced design system IS
            its own regulatory audit trail.

ASM-D009: The average design payload (geometry + metadata per operation) is
          ≤ 50KB. Large artifacts (full assembly models, simulation meshes,
          rendered images) stored by reference in Content Store.
          — Rationale: Statistical analysis of SRC-D016 (99th percentile).
            Parametric definitions are compact; tessellated representations
            are large. The system stores parametric definitions inline and
            tessellated representations by reference.

ASM-D010: The system MUST be implementable as a protocol, not only as a product.
          — Rationale: Same as all peer substrates. Engineering design cannot
            depend on a single vendor's platform. Multiple interoperable
            implementations must be possible. This is doubly critical for
            DESIGN because design data must outlive any vendor (ASM-D012).

ASM-D011: Tolerance management is the single most impactful quality concern in
          physical artifact design.
          — Rationale: Analysis of SRC-D009, SRC-D016. 31% of manufacturing
            defects trace to tolerance stack-up errors. GD&T (ASME Y14.5)
            exists because individual dimension tolerances are necessary but
            not sufficient — the assembly-level stack-up determines whether
            parts fit. Tolerance (TERM-D011) is a first-class primitive with
            mandatory stack-up analysis capabilities.

ASM-D012: Design data has the longest consequence horizon of any substrate.
          — Rationale: Aircraft certification data: 30+ years beyond end of
            production. Building structural calculations: 100+ years. Bridge
            design: the lifetime of the structure (potentially centuries).
            Nuclear facility design basis: millennia. DESIGN persistence
            requirements exceed those of any peer substrate. This drives
            format-independence requirements (no proprietary binary formats
            for long-term storage).
```

### 0.3 Unknowns

```
UNK-D001: Quantum computing impact on design optimization. Quantum algorithms
          for combinatorial optimization (QAOA, quantum annealing) may
          fundamentally change how design space exploration works.
          — Impact: Does not affect primitives. May affect COMPUTE integration
            (INT-D003) if quantum solvers require different input formats.
            Deferred to v1.1.

UNK-D002: Parametric constraint solver performance at scale. Complex
          assemblies (10,000+ components, 100,000+ constraints) may exceed
          real-time solver capability.
          — Impact: Performance is implementation-dependent, not specification-
            dependent. The spec defines the contract (constraints must be
            satisfied); the implementation chooses the solver. Section 17
            provides operational profile targets.

UNK-D003: AI-generated geometry verification. When AI agents generate novel
          geometries (topology optimization, generative design), how to verify
          that the result satisfies all constraints without exhaustive
          simulation?
          — Impact: Affects DesignEnvelope (TERM-D024) enforcement. AI-generated
            designs MUST pass the same TestCriteria as human-generated designs.
            No shortcut. The question is efficiency, not correctness.

UNK-D004: Cross-domain design language unification. Can a single parametric
          language express molecular geometry, IC layout, mechanical
          assemblies, and building structures without domain-specific
          extensions?
          — Impact: Geometry (TERM-D006) handles this via representation_type
            enum. The underlying entity is domain-independent; the representation
            is domain-specific. Complete unification at the representation level
            is a non-goal; unification at the entity level is achieved.

UNK-D005: Intellectual property protection at the specification level. Design
          data is commercially sensitive. How to enable cross-organization
          collaboration (supply chain) while protecting IP?
          — Impact: Section 10 (Security & Privacy) addresses this with
            IP-classification levels and need-to-know access. The fundamental
            tension between collaboration and IP protection is organizational,
            not technical.

UNK-D006: Living design documents. Buildings and infrastructure are modified
          throughout their operational life. How does the design record evolve
          after the original design team is gone?
          — Impact: DesignVersion (TERM-D016) and ChangeOrder (TERM-D017)
            support post-deployment design evolution. The design record is a
            living document linked to PHYSICAL's PhysicalAsset (TERM-P017).
            The as-built and as-maintained configurations are first-class.

UNK-D007: Biomimetic and bio-inspired design representation. Designs inspired
          by biological structures (bone-like lattices, shark-skin surfaces,
          neural architectures) may require representation types not in the
          initial enum.
          — Impact: Geometry representation_type enum is extensible. New types
            (bio_lattice, fractal, etc.) can be added without schema changes.
            Deferred to v1.1.

UNK-D008: Process design (P&ID) boundary with PHYSICAL.
          — Impact: RESOLVED in this version. Working boundary: DESIGN owns the
            P&ID (process specification, equipment sizing, instrument selection,
            piping/vessel design). PHYSICAL owns the control strategy, runtime
            execution, and sensor/actuator configuration. The handoff is:
            DESIGN's process specification → PHYSICAL's Process entity
            (TERM-P019) + Sensor/Actuator/ControlLoop configuration. DESIGN
            specifies what equipment is needed and how it connects; PHYSICAL
            operates it.
```

---

## 1. SYSTEM INTENT (WHY)

### Problem Statement

Humanity has produced approximately 2.3 million distinct designed artifacts
currently in active production, maintenance, or operation — spanning mechanical
parts, electronic assemblies, buildings, infrastructure, molecules, and
integrated systems. These artifacts are specified, analyzed, reviewed, versioned,
and released using 1,100+ incompatible design tool platforms, each implementing
the same 28 fundamental patterns using mutually incomprehensible data models,
file formats, and workflows.

The consequences are catastrophic:
- 31% of manufacturing defects trace to tolerance stack-up errors that could
  have been detected in design (SRC-D016).
- 23% of change orders are caused by requirements that were testable but
  untested — intent was present but never formalized (SRC-D016).
- 18% of project delays are caused by interface mismatches between subsystems
  designed in different tools (SRC-D016).
- 67% of design reviews require 2+ cycles because review comments cannot be
  formally linked to requirements, constraints, and analysis results (SRC-D016).
- 12% of all change orders are triggered by material substitutions where the
  original material selection rationale was lost (SRC-D016).

An AI agent that can manage a business (via SUBSTRATE), reason about physics
(via KNOWLEDGE), run a simulation (via COMPUTE), coordinate with engineers (via
COMMUNICATION), and operate equipment (via PHYSICAL) still cannot design a
bracket, specify a circuit, or create a building plan. SUBSTRATE-DESIGN closes
this gap.

### Primary Actors

```
ACT-D001: Human Designer
          — Goal: Create, modify, and document design artifacts — geometry,
            materials, assemblies, drawings, BOMs. Define requirements. Record
            rationale. Navigate design space.
          — Trust level: trusted (authenticated, authorized per Role, full
            access within assigned design scope)

ACT-D002: Human Engineer (Analysis)
          — Goal: Perform design verification — structural analysis, thermal
            analysis, tolerance stack-up, electromagnetic simulation, DRC/ERC,
            code compliance checking. Validate that designs meet requirements.
          — Trust level: trusted (elevated privileges for analysis configuration,
            all analysis assumptions audit-logged)

ACT-D003: Human Design Authority
          — Goal: Approve designs at maturity gates. Authorize change orders.
            Accept or reject design review findings. Release designs for
            manufacturing. Sign regulatory submissions.
          — Trust level: trusted (approval authority per scope, all decisions
            audit-logged with justification, cannot be delegated to AI agents
            for safety-critical or regulatory artifacts)

ACT-D004: AI Agent (Narrow Design)
          — Goal: Execute specific design tasks autonomously within a defined
            DesignEnvelope — parametric variation, tolerance analysis, DRC
            execution, BOM generation, drawing annotation, component selection
            from approved lists, routine standards compliance checking
          — Trust level: partially trusted (bounded to pre-validated design
            scope, all outputs require human review before release, mandatory
            traceability of all decisions to requirements and constraints)

ACT-D005: AI Agent (General Design)
          — Goal: Explore design spaces, perform topology optimization, generate
            design alternatives, propose material selections, identify
            constraint conflicts, draft requirement decompositions, assist in
            trade studies
          — Trust level: partially trusted (expanded DesignEnvelope, mandatory
            human approval for: design release, safety-critical design decisions,
            material selections for regulated artifacts, any deviation from
            referenced standards)

ACT-D006: External System (CAD/EDA/BIM)
          — Goal: Exchange design data with SUBSTRATE-DESIGN via integration
            endpoint. Import/export geometry, BOMs, requirements, analysis
            results via STEP, IFC, IPC-2581, EDIF, GDSII, OSLC, ReqIF formats.
          — Trust level: untrusted (all inputs validated against declared schemas,
            imported geometry verified for topological validity, imported
            requirements checked for testability, rate-limited, sandboxed)

ACT-D007: Auditor (Design)
          — Goal: Verify regulatory compliance, design history file completeness,
            traceability from requirements through analysis to test evidence.
            Review change order records. Audit configuration baselines.
          — Trust level: trusted (read-all within scope, time-travel access to
            all design event histories, cannot modify design artifacts)

ACT-D008: Manufacturing System
          — Goal: Consume released design data — drawings, BOMs, fabrication
            methods, work instructions — to produce physical artifacts.
            Report manufacturing deviations back to design for disposition.
          — Trust level: partially trusted (read access to released artifacts
            only, cannot modify design data, deviation reports validated
            against design tolerances)
```

### Success Definition

SUBSTRATE-DESIGN succeeds when a single specification enables any conforming
implementation to: capture all requirements for a designed artifact, define its
geometry and materials at any scale, constrain the solution space, verify against
test criteria, manage configuration and change, and release manufacturing
instructions — across all design domains (mechanical, electronic, architectural,
molecular, systems) — without requiring domain-specific design tools for the
specification logic, proprietary file formats for long-term storage, or
manual traceability between requirements and test evidence.

### Non-Goals

```
NG-D001: SUBSTRATE-DESIGN does NOT replace CAD kernels, geometric modeling
         engines, or parametric solvers. DESIGN defines the entity model for
         design artifacts; specialized tools provide the geometric computation.
         DESIGN stores the result; the solver is external.

NG-D002: SUBSTRATE-DESIGN does NOT replace simulation solvers (FEA, CFD, EM,
         molecular dynamics). COMPUTE (via Pipelines) runs simulations.
         DESIGN assembles the simulation inputs (geometry + material +
         constraints + boundary conditions) and consumes the results
         (AnalysisResult). The boundary is the simulation request.

NG-D003: SUBSTRATE-DESIGN does NOT replace rendering engines, visualization
         tools, or interactive 3D viewers. BUSINESS Views consume DESIGN
         data feeds. DESIGN defines the data model; presentation is external.

NG-D004: SUBSTRATE-DESIGN does NOT replace ERP/MRP production planning and
         scheduling. BUSINESS owns production scheduling. DESIGN provides the
         BillOfMaterials and FabricationMethod; production planning consumes
         them.

NG-D005: SUBSTRATE-DESIGN does NOT operate physical equipment. PHYSICAL
         operates what DESIGN specifies. DESIGN creates the P&ID; PHYSICAL
         configures the sensors, actuators, and control loops. DESIGN specifies
         new equipment; PHYSICAL operates existing equipment.

NG-D006: SUBSTRATE-DESIGN does NOT replace materials science research.
         KNOWLEDGE owns material property truth (Propositions with confidence).
         DESIGN consumes material properties and records which values were used
         in design decisions. If testing reveals a material property is wrong,
         DESIGN emits an event; KNOWLEDGE updates the Proposition.

NG-D007: SUBSTRATE-DESIGN does NOT define safety engineering methodology
         (HAZOP facilitation, SIL determination, FMEA process). It provides
         the data model for recording and enforcing the results of safety
         engineering. PHYSICAL owns SafetyFunction and SafetyEnvelope enforcement.
```

### Failure Definition

SUBSTRATE-DESIGN fails if any conforming implementation permits: (a) a design
artifact to be released for manufacturing without all Requirements having at
least one linked TestCriterion with a recorded result, (b) a Configuration to
be declared valid when it contains Components whose interface constraints are
mutually incompatible, (c) a ChangeOrder to be approved without impact analysis
showing which other Components, Assemblies, and Configurations are affected,
(d) a tolerance stack-up to pass when individual tolerances are valid but the
assembly-level stack exceeds specification, or (e) any loss of the append-only
Event log that constitutes the regulatory design history file.

---

## 2. SYSTEM BOUNDARIES (WHERE IT STOPS)

### 2.1 Dependencies

```
DEP-D001: Time Source
          — Purpose: Temporal ordering of design events. Design operations are
            human-timescale (seconds to days), not real-time. Standard
            NTP synchronization sufficient.
          — Failure impact: Events timestamped with uncertainty interval.
            Design operations continue with local clocks. No safety impact.

DEP-D002: Identity Verification Provider
          — Purpose: Establishing Actor identity before permitting design
            modifications. Shared with all substrates per CROSS-SUBSTRATE-
            CONVENTIONS.md §1.
          — Failure impact: New authentications blocked. Existing sessions
            continue. Read-only access continues. No new design modifications
            from unverified sessions.

DEP-D003: Content Store
          — Purpose: Large artifacts — full assembly models (tessellated),
            simulation meshes, rendered images, CAD native files, fabrication
            files (Gerber, G-code, GDSII). Anything exceeding the inline
            payload limit (ASM-D009: 50KB).
          — Failure impact: Metadata accessible. Binary content temporarily
            unreadable. Design review may be impaired (cannot view full
            geometry). No data loss (metadata + parametric definitions inline).

DEP-D004: SUBSTRATE (Business)
          — Purpose: Organization scoping, agent identity, project management,
            financial tracking (BOM cost rollup), document management,
            compliance obligations. See CROSS-SUBSTRATE-CONVENTIONS.md §2.
          — Failure impact: Design operations continue independently. Business
            cross-references (cost data, project schedules) unresolvable until
            restored. New agent authorization blocked. Existing authorizations
            cached locally.

DEP-D005: SUBSTRATE-KNOWLEDGE
          — Purpose: Material property data (Propositions with confidence),
            epistemic provenance of design decisions, standards interpretation,
            prior design knowledge. Material (TERM-D008) properties linked to
            Knowledge Propositions (TERM-K001).
          — Failure impact: Design operations continue using cached material
            data. New material property queries fail. Material confidence
            updates not received. Designs using stale material data flagged
            with warning. No safety impact (cached data is conservative).

DEP-D006: SUBSTRATE-COMPUTE
          — Purpose: Simulation execution (FEA, CFD, EM, molecular dynamics,
            topology optimization), generative design exploration, parametric
            sweeps, tolerance Monte Carlo analysis.
          — Failure impact: New analyses cannot be submitted. Existing
            AnalysisResults remain valid. Design proceeds with prior analysis.
            Release blocked if mandatory analyses incomplete.

DEP-D007: SUBSTRATE-COMMUNICATION
          — Purpose: Structured discourse for design reviews (DesignReview →
            Discourse), change order approval workflows (ChangeOrder →
            Commitment/Consensus), interface negotiation between subsystem
            teams, design clarification (Annotation promotion to Speech Act).
          — Failure impact: Design reviews degrade to unstructured comments
            (stored as Annotations). Change order approvals queue. Interface
            negotiations queue. Design creation and modification continue.

DEP-D008: SUBSTRATE-PHYSICAL
          — Purpose: Physical instantiation of designs. Component (TERM-D004)
            becomes PhysicalAsset (TERM-P017) when manufactured. FabricationMethod
            (TERM-D020) informs Process (TERM-P019). Tolerance (TERM-D011)
            verified by Measurement (TERM-P002) and Calibration (TERM-P006).
            AnalysisResult validated against DigitalTwin (TERM-P023).
          — Failure impact: Manufacturing handoff blocked. Design creation and
            modification continue. As-built feedback from PHYSICAL unavailable.

DEP-D009: Material & Standards Databases
          — Purpose: Authoritative material property data (ASTM, manufacturer
            datasheets), regulatory standards (ASME, ISO, IPC, IEEE, Eurocode),
            component libraries (electronic parts, fasteners, structural
            sections). These are external reference data consumed by DESIGN.
          — Failure impact: New material/standard lookups fail. Cached data
            continues. Designs referencing uncached materials/standards blocked
            until restored.

DEP-D010: SUBSTRATE-GOVERNANCE — Norm (TERM-G001) provides regulatory
            requirements for design reviews and submissions. ComplianceAssessment
            (TERM-G009) provides regulatory approval status. RegulatoryChange
            (TERM-G025) tracks standard lifecycle changes affecting design.
          — Failure impact: Regulatory submission blocked. Design operations
            continue. Compliance status cached.

DEP-D011: SUBSTRATE-TEMPORAL — Schedule (TERM-T010) provides production
            scheduling from BOMs. Activity (TERM-T007) provides design review
            meeting slots. Booking (TERM-T004) confirms resource allocation.
          — Failure impact: Production scheduling blocked. Design creation and
            modification continue. Review scheduling deferred.

DEP-D012: SUBSTRATE-SPATIAL — Location (TERM-S002) provides site context
            for design placement. SpatialConstraint (TERM-S019) provides setback,
            flood zone, and utility corridor data. SpatialGeometry (TERM-S004)
            provides Earth-referenced coordinates for local design geometry.
          — Failure impact: Site placement blocked. Design operations continue
            with local coordinates only.
```

### 2.2 Explicit Exclusions

```
SUBSTRATE-DESIGN does NOT replace:
  — Geometric modeling kernels (Parasolid, ACIS, OpenCASCADE) → external solvers
  — Parametric constraint solvers → external computation
  — FEA/CFD/EM simulation solvers (→ COMPUTE Pipelines)
  — Rendering engines and 3D visualization (→ external presentation)
  — ERP/MRP production planning (→ BUSINESS workflows)
  — Physical equipment operation (→ PHYSICAL sensors/actuators/control)
  — Materials science research (→ KNOWLEDGE propositions)
  — Safety engineering methodology (HAZOP, SIL, FMEA → process, not data model)
  — Device firmware or embedded control (→ PHYSICAL via FieldbusAdapter)
  — Construction project management scheduling (→ BUSINESS)

SUBSTRATE-DESIGN DOES replace:
  — The data model beneath every CAD/CAM/CAE platform
  — The data model beneath every EDA platform
  — The data model beneath every BIM platform
  — The data model beneath every PLM system
  — Every proprietary BOM structure
  — Every proprietary change management workflow model
  — Every proprietary configuration management data model
  — Every proprietary requirements traceability matrix
  — Every proprietary design review record format
  — Every proprietary tolerance specification format
  — The gap between "design intent" and "manufacturing instruction"
```

### 2.3 Trust Boundaries

```
TRUST-D001: All inputs from ACT-D006 (External System) are UNTRUSTED. Imported
            geometry validated for topological validity (watertight, no self-
            intersections for solid models). Imported requirements validated for
            testability. Imported BOMs validated for completeness and circular
            reference detection. Rate-limited. Sandboxed.

TRUST-D002: All inputs from ACT-D004/D005 (AI Agents) are PARTIALLY TRUSTED.
            Bounded by DesignEnvelope. All AI-generated design artifacts must
            satisfy the same TestCriteria and pass the same DesignReviews as
            human-generated artifacts. No shortcuts. AI design authority scoped
            to assigned Components/Assemblies within envelope.

TRUST-D003: Material property data from DEP-D005 (KNOWLEDGE) is CONDITIONALLY
            TRUSTED. Trust level = Knowledge confidence. Design decisions using
            material data below confidence threshold require explicit
            acknowledgment and safety margin increase. Material data with
            confidence < 0.5 cannot be used for safety-critical designs.

TRUST-D004: Analysis results from DEP-D006 (COMPUTE) are CONDITIONALLY TRUSTED.
            Trust level depends on: mesh convergence study completed, boundary
            conditions reviewed, solver validation (benchmark comparison). Blind
            trust in simulation results is a forbidden state.

TRUST-D005: External standards and material databases from DEP-D009 are TRUSTED
            within their declared scope and version. Standards are immutable
            once referenced — a design referencing ASME Y14.5-2018 always means
            the 2018 edition, regardless of subsequent revisions.
```

### 2.4 Network Boundaries

```
Local:         Designer workstation. Geometry editing, parametric modification,
               interactive constraint solving. Sub-second response required for
               interactive design operations. Offline-capable for geometry work.

Organization:  On-premise or private cloud. Design data repository, BOM
               management, configuration control, design review workflows,
               analysis job submission. All design data for an Organization
               resides here. Cross-team collaboration.

Supply chain:  Cross-organization. Controlled exchange of design data between
               OEM and suppliers. IP-protected. Need-to-know access only.
               Supplier sees only their assigned Component scope. OEM sees
               supplier's interface compliance, not internal design details.

Federation:    Cross-organization standards sharing. Shared component libraries
               (e.g., standard fasteners, common electronic parts). Anonymized
               design quality metrics. NO proprietary design data crosses
               federation boundary without explicit bilateral authorization.
```

### 2.5 Runtime Assumptions

```
Design operations are human-timescale with two exceptions:

  Interactive modeling → Sub-second parametric update on local workstation.
                         Constraint solver performance is implementation-
                         dependent. Target: < 500ms for assemblies up to
                         1,000 components. Large assemblies (10,000+) may
                         require incremental solving.

  Batch operations    → Analysis submission, BOM derivation, DRC execution,
                         tolerance stack-up Monte Carlo — may take minutes to
                         hours. Executed via COMPUTE Pipelines. Results consumed
                         asynchronously.

  All other operations (requirement creation, review, change order, release)
  are human-timescale (seconds to minutes). No real-time requirements.

Deployment:   Organization-level. No edge tier required (unlike PHYSICAL).
              Local workstation caching for offline geometry editing.
Language:     UNKNOWN — implementation-agnostic. Specification defines protocol.
Storage:      Design data format MUST be open, documented, and parseable without
              proprietary tools (ASM-D010, ASM-D012). Long-term storage in
              non-proprietary formats (STEP, IFC, open JSON/protobuf schemas).
```

---

## 3. GLOSSARY (PRIMITIVES)

> 28 terms. Every term is a primitive — the minimal, non-decomposable concept
> required to specify any designed artifact at any scale in any domain. If a
> term can be expressed as a composition of other terms, it is not a primitive.
> Each of these 28 survived the reduction from 347 candidate concepts extracted
> from 1,100+ design tool implementations.

### Intent & Requirements

```
TERM-D001: Requirement = An atomic, testable statement of what a designed
           artifact must do, be, or satisfy. Has: requirement_id (UUID),
           specification_id (UUID — parent Specification), type (enum:
           functional | performance | interface | environmental | regulatory |
           safety | reliability | manufacturability | cost), statement (text —
           the requirement in natural language), rationale (text — why this
           requirement exists), priority (enum: shall | should | may),
           testable (boolean — MUST be true for release), parent_requirement_id
           (UUID? — for decomposition), version (integer), status (enum:
           draft | active | superseded | deleted), created_by (agent_id),
           created_at (timestamp).
           — What every "shall statement" in a requirements document, every
             "acceptance criterion" in a user story, every "design input" in
             an FDA DHF, every "performance specification" in a MIL-STD TDP,
             and every "functional requirement" in a SysML model actually is.
           — A Requirement is NOT a wish, a goal, or a suggestion. It is a
             formal constraint on the solution space with a binary evaluation:
             satisfied or not satisfied, determined by TestCriterion (TERM-D013).
           — Decomposition: Requirements decompose into child Requirements.
             The parent is satisfied if and only if all children are satisfied.
           — Source: SRC-D007, SRC-D008, SRC-D015, ASM-D002

TERM-D002: Specification = A versioned, complete collection of Requirements,
           Constraints, TestCriteria, and referenced Standards that together
           define what an artifact must be. Has: specification_id (UUID),
           name (string), description (text), version (integer), status (enum:
           draft | in_review | approved | released | superseded | withdrawn),
           artifact_type (enum: component | assembly | system | material |
           process), domain (enum: mechanical | electronic | architectural |
           molecular | systems | multi_domain), maturity_level (enum:
           conceptual | preliminary | detailed | released | as_built),
           requirements[] (Requirement refs), constraints[] (Constraint refs),
           test_criteria[] (TestCriterion refs), standards[] (Standard refs),
           created_by (agent_id), approved_by (agent_id?), approved_at
           (timestamp?), organization_id (UUID).
           — What every "product specification," "engineering specification,"
             "IFC model view definition," "device specification," and
             "molecular target profile" actually is.
           — A Specification without TestCriteria is incomplete. A Specification
             with untested Requirements cannot be released (Failure Definition).
           — CROSS-SUBSTRATE NOTE: A released Specification may be linked to a
             BUSINESS Document (TERM-019) for organizational tracking and to a
             PHYSICAL SafetyEnvelope (TERM-P014) when the artifact has safety
             implications.
           — Source: SRC-D007, SRC-D008, SRC-D014, SRC-D015

TERM-D003: DesignRationale = An immutable record of why a design decision was
           made, linking the decision to the evidence, constraints, trade-offs,
           and alternatives considered. Has: rationale_id (UUID), entity_type
           (string — what entity this rationale applies to), entity_id (UUID),
           decision (text — what was decided), alternatives_considered (text[] —
           what else was evaluated), selection_criteria (text — why this
           alternative was chosen), evidence_refs (cross-substrate Reference[] —
           links to KNOWLEDGE Arguments, AnalysisResults, test data),
           trade_offs (text — what was sacrificed), constraints_active
           (Constraint refs — which constraints drove the decision), decided_by
           (agent_id), decided_at (timestamp).
           — What every "design justification" in a DHF, every "trade study
             conclusion," every "engineering judgment" recorded in meeting
             minutes, and every "basis of design" document actually is.
           — DesignRationale is IMMUTABLE. Decisions can be superseded by new
             decisions (via ChangeOrder), but the original rationale is never
             modified. This is the audit trail for "why was it designed this
             way?"
           — CROSS-SUBSTRATE NOTE: DesignRationale.evidence_refs links to
             KNOWLEDGE Arguments (TERM-K015) and Evidence. The rationale IS
             the design-domain manifestation of structured argumentation.
           — Source: SRC-D016 (12% of change orders from lost rationale),
             SRC-D013, ASM-D002
```

### Structure & Geometry

```
TERM-D004: Component = A discrete, identifiable part that can be independently
           specified, manufactured, tested, and replaced. The atomic unit of
           design composition. Has: component_id (UUID), name (string),
           part_number (string — organization-scoped), specification_id (UUID —
           governing Specification), geometry_id (UUID? — Geometry if physical),
           material_id (UUID? — Material if physical), current_version (integer),
           status (enum: concept | in_design | in_review | released |
           production | obsolete), domain (enum: mechanical | electronic |
           architectural | molecular | software_hardware | multi_domain),
           parent_assembly_id (UUID? — if part of an Assembly),
           fabrication_method_id (UUID? — how to make it), mass (decimal?),
           cost_estimate (decimal?), organization_id (UUID).
           — What every "part" in a CAD system, every "component" in an EDA
             schematic, every "element" in a BIM model, every "molecule" in a
             molecular design tool, and every "CSCI" in a systems engineering
             model actually is.
           — A Component without a Specification is an orphan. A Component
             without a Geometry (for physical artifacts) is incomplete. A
             Component without a Material (for physical artifacts) is
             unmanufacturable.
           — CROSS-SUBSTRATE NOTE: When manufactured, a Component becomes a
             PHYSICAL PhysicalAsset (TERM-P017). The link is maintained via
             cross-substrate Reference. DESIGN owns the specification; PHYSICAL
             owns the operational instance.
           — Source: SRC-D001, SRC-D002, SRC-D003, SRC-D004

TERM-D005: Assembly = A composed structure of Components with defined spatial
           relationships, interface connections, and configuration rules. Has:
           assembly_id (UUID), name (string), assembly_number (string),
           specification_id (UUID), components[] (Component refs with
           quantity, position, orientation), sub_assemblies[] (Assembly refs —
           recursive), interfaces[] (Interface refs — connections between
           components), geometry_id (UUID? — assembly-level geometry/envelope),
           configuration_id (UUID? — valid version combination), current_version
           (integer), status (same enum as Component), bom_id (UUID? — derived
           BillOfMaterials), organization_id (UUID).
           — What every "assembly" in a CAD system, every "board" in an EDA
             tool, every "building model" in BIM, every "complex" in molecular
             design, and every "system" in systems engineering actually is.
           — Assembly is recursive: an Assembly may contain sub-Assemblies.
           — An Assembly's BillOfMaterials (TERM-D021) is derivable from its
             component tree but may be overridden for manufacturing purposes
             (eBOM vs mBOM distinction).
           — Constraint propagation: Constraints on the Assembly propagate to
             Components. Constraints on Components propagate to the Assembly
             (bidirectional — Property D6: Constraint Primacy).
           — Source: SRC-D001, SRC-D003, SRC-D004, SRC-D007

TERM-D006: Geometry = A representation-independent description of physical shape
           and spatial extent. Has: geometry_id (UUID), entity_id (UUID — the
           Component or Assembly this describes), representation_type (enum:
           brep | mesh | parametric | implicit | point_cloud | 2d_profile |
           schematic | layout_2d | molecular_graph | voxel | quantum_structure),
           coordinate_system (enum: cartesian | cylindrical | spherical |
           fractional_crystal | internal_molecular), units (enum: m | mm | um |
           nm | angstrom | mil | inch), bounding_box (6 decimals — min/max xyz),
           content_ref (content_store_ref — actual geometry data), content_hash
           (SHA-256 — integrity), parameter_count (integer — for parametric),
           face_count (integer? — for brep/mesh), version (integer).
           — What every "solid body" in MCAD, every "layout" in EDA, every
             "3D model" in BIM, every "molecular structure" in chemistry,
             every "topology" in 3D printing, and every "mesh" in simulation
             actually is.
           — Scale examples (Property D4 — Scale Spanning):
             quantum_structure: angstrom scale (molecular orbitals)
             molecular_graph: angstrom to nanometer (drug molecules, polymers)
             layout_2d: nanometer to millimeter (IC physical design)
             schematic: logical (circuit topology, no physical dimensions)
             2d_profile: micrometer to meter (sheet metal, PCB cross-sections)
             brep: micrometer to kilometer (mechanical parts to infrastructure)
             mesh: any scale (simulation discretization)
             parametric: any scale (equation-driven, unit-aware)
             voxel: micrometer to meter (3D printing, medical imaging)
             point_cloud: millimeter to kilometer (3D scanning, surveying)
           — Geometry is NOT Drawing (TERM-D022). Geometry is the 3D/abstract
             shape. Drawing is the 2D annotated production representation
             derived FROM geometry.
           — CROSS-SUBSTRATE NOTE: Geometry data is stored in Content Store
             (DEP-D003) by reference. DESIGN stores the metadata (type, units,
             hash, parameters); the binary geometry data lives in Content Store.
             When submitted for simulation, Geometry + Material + Constraints
             compose into a COMPUTE Pipeline input (see FLOW-D003).
           — Source: SRC-D001, SRC-D002, SRC-D003, SRC-D006, ASM-D003

TERM-D007: Topology = The abstract connectivity and relationships between
           Components independent of geometry. Has: topology_id (UUID),
           assembly_id (UUID — parent Assembly), nodes[] (Component/Assembly
           refs), edges[] (Interface refs — connections between nodes),
           topology_type (enum: spatial | electrical | thermal | fluid |
           structural | signal | power | logical), constraints[]
           (Constraint refs — topological constraints like "A must be adjacent
           to B"), version (integer).
           — What every "schematic netlist" in EDA, every "P&ID connection
             diagram" in process engineering, every "cable schedule" in
             electrical engineering, every "piping isometric connectivity" in
             plant design, and every "system architecture diagram" in systems
             engineering actually is.
           — Topology is independent of Geometry. Two designs may have
             identical Topology (same connections) but different Geometry
             (different physical layout). This separation is fundamental to
             EDA (schematic vs layout) and systems engineering (logical vs
             physical architecture).
           — Source: SRC-D002, SRC-D007, SRC-D003
```

### Material & Properties

```
TERM-D008: Material = A characterized substance or composite from which
           Components are fabricated. Has: material_id (UUID), name (string),
           designation (string — e.g., "AISI 316L", "FR-4", "ABS",
           "C60H84N20O18S2"), material_class (enum: metal | polymer | ceramic |
           composite | semiconductor | biological | chemical | glass | wood |
           natural_fiber | metamaterial), properties[] (MaterialProperty refs),
           standards[] (Standard refs — material specifications),
           data_source (enum: tested | literature | simulation | estimated),
           knowledge_proposition_ref (cross-substrate Reference? — link to
           KNOWLEDGE Proposition for confidence), organization_id (UUID).
           — What every "material" in a CAD material library, every "substrate"
             in EDA, every "material layer" in BIM, every "ligand" in
             molecular design, and every "raw material" in a BOM actually is.
           — Material is NOT MaterialProperty (TERM-D009). Material is the
             substance; MaterialProperty is a measurable characteristic of that
             substance under specified conditions. Steel is a Material; its
             yield strength at 20°C is a MaterialProperty.
           — CROSS-SUBSTRATE NOTE: Material properties link to KNOWLEDGE
             Propositions (TERM-K001) with confidence. KNOWLEDGE owns the
             truth of "the yield strength of 316L is 205 MPa." DESIGN
             consumes this value and records which value was used in which
             design decision (via DesignRationale). If testing reveals the
             actual value differs, DESIGN emits a
             substrate.design.material.property_discrepancy event; KNOWLEDGE
             updates the Proposition.
           — Source: SRC-D008 (ASTM material specs), SRC-D010, SRC-D006

TERM-D009: MaterialProperty = A measurable characteristic of a Material under
           specified conditions. Has: property_id (UUID), material_id (UUID),
           property_type (enum: mechanical | thermal | electrical | optical |
           magnetic | chemical | biological | acoustic | density | cost),
           property_name (string — e.g., "yield_strength", "thermal_conductivity",
           "dielectric_constant", "binding_affinity"), value (decimal),
           unit (string — SI unit), conditions (object — temperature, pressure,
           strain rate, frequency, humidity, etc.), uncertainty (decimal? —
           measurement uncertainty), source (enum: tested | published |
           simulated | interpolated), test_method (string? — e.g., "ASTM E8",
           "IPC-TM-650 2.4.24"), confidence (decimal? — from KNOWLEDGE),
           valid_range (object? — min/max for temperature, etc.).
           — What every "material property" in a datasheet, every "substrate
             parameter" in EDA, every "thermal transmittance" in BIM energy
             models, and every "calculated binding energy" in molecular
             design actually is.
           — Properties are condition-dependent. "Yield strength of 316L" is
             meaningless without temperature. MaterialProperty always carries
             conditions.
           — Source: SRC-D008, SRC-D009, SRC-D006
```

### Constraints & Standards

```
TERM-D010: Constraint = A formal limitation that restricts the design space.
           Has: constraint_id (UUID), entity_id (UUID — what entity this
           constrains), entity_type (string), constraint_type (enum:
           dimensional | geometric | structural | thermal | electrical |
           electromagnetic | chemical | regulatory | cost | mass | power |
           manufacturing | interface | environmental | safety),
           expression (text — formal expression of the constraint, machine-
           parseable where possible), verification_method (enum:
           manual_inspection | analysis | simulation | automated_rule_check |
           demonstration | certification | test), severity (enum: mandatory |
           preferred | guidance), status (enum: active | waived | superseded),
           waiver_justification (text? — required if waived), source
           (string — which Requirement, Standard, or physics drives this),
           version (integer).
           — What every "design constraint" in a requirements doc, every
             "design rule" in EDA DRC/ERC, every "clash detection rule" in
             BIM, every "bond length constraint" in molecular design, every
             "code check" in structural engineering, and every "clearance
             requirement" in a PCB layout actually is.
           — Design Rule Checks (DRC in EDA, clash detection in CAD, code
             checks in BIM) are Constraints with verification_method:
             automated_rule_check and a machine-executable expression. This
             eliminates the need for a separate "DesignRule" primitive.
           — Constraints propagate bidirectionally through Assemblies
             (Property D6). A constraint on a child Component may constrain
             the parent Assembly, and vice versa.
           — CROSS-SUBSTRATE NOTE: Constraints link to KNOWLEDGE Propositions
             (TERM-K001) when the constraint is derived from scientific
             knowledge (e.g., "maximum operating temperature of this polymer
             is 150°C" is a Knowledge Proposition that becomes a Design
             Constraint).
           — Source: SRC-D001, SRC-D002, SRC-D003, SRC-D007, SRC-D008

TERM-D011: Tolerance = The permissible variation in a dimension, property, or
           behavior. Has: tolerance_id (UUID), entity_id (UUID — Component or
           Assembly), tolerance_type (enum: dimensional | geometric_form |
           geometric_orientation | geometric_location | geometric_runout |
           geometric_profile | surface_finish | position_true | statistical |
           material_property | performance), nominal_value (decimal),
           upper_limit (decimal), lower_limit (decimal), unit (string),
           datum_refs (string[]? — GD&T datum features), material_condition
           (enum: mmc | lmc | rfs | none — per ASME Y14.5), statistical_model
           (enum: normal | uniform | beta | empirical | none),
           cpk_target (decimal? — process capability target), stack_analysis_id
           (UUID? — link to assembly-level stack-up analysis), version (integer).
           — What every "tolerance" on a drawing, every "clearance specification"
             in EDA, every "construction tolerance" in BIM, every "purity
             specification" in chemistry, and every "acceptable range" in any
             engineering specification actually is.
           — Tolerance is NOT Constraint (TERM-D010). A Constraint says "X must
             be ≤ 100mm." A Tolerance says "X is 95mm ±0.5mm." Constraints
             define the boundary; Tolerances define the allowable variation
             within it.
           — ASM-D011: 31% of manufacturing defects trace to tolerance stack-up
             errors. Individual part tolerances may be met while the assembly
             fails. Assembly-level stack-up analysis is MANDATORY (CAP-D016).
           — CROSS-SUBSTRATE NOTE: Tolerance values are verified by PHYSICAL
             Measurements (TERM-P002) using calibrated instruments
             (Calibration TERM-P006). The feedback loop: DESIGN specifies
             tolerance → PHYSICAL measures actual → comparison determines
             conformance.
           — Source: SRC-D009, SRC-D010, ASM-D011

TERM-D012: Standard = A referenced external normative document that constrains
           the design. Has: standard_id (UUID), designation (string — e.g.,
           "ASME Y14.5-2018", "IPC-A-610G", "EN 1993-1-1:2005"),
           issuing_body (string — e.g., "ASME", "IPC", "CEN"), title (string),
           version (string), effective_date (date), status (enum: current |
           superseded | withdrawn), scope (text — what the standard covers),
           clauses_referenced (string[] — specific sections used),
           content_ref (content_store_ref? — full text if licensed),
           superseded_by (standard_id? — if superseded).
           — What every "applicable standard" in a specification, every
             "code reference" in structural engineering, every "IPC class"
             in electronics, and every "pharmacopoeia reference" in
             pharmaceutical design actually is.
           — Standards are IMMUTABLE once referenced. A design referencing
             ASME Y14.5-2018 always means the 2018 edition. When a standard
             is superseded, existing designs continue referencing the original;
             ChangeOrders assess whether migration to the new edition is
             required.
           — CROSS-SUBSTRATE NOTE: Standards are registered as Sources
             (TERM-K020) in KNOWLEDGE. The authoritative interpretation of a
             standard clause is a Knowledge Proposition.
           — Source: SRC-D008, SRC-D015
```

### Verification & Validation

```
TERM-D013: TestCriterion = A formal, testable condition that determines whether
           a Requirement is satisfied. Has: criterion_id (UUID),
           requirement_id (UUID — the Requirement this tests), description
           (text — what is being tested), test_method (enum: analysis |
           simulation | inspection | demonstration | test | similarity),
           acceptance_condition (text — pass/fail criteria, machine-parseable
           where possible), result_value (decimal? — measured/computed value),
           result_status (enum: untested | pass | fail | inconclusive),
           result_evidence_ref (cross-substrate Reference? — link to
           AnalysisResult or PHYSICAL Measurement), tested_by (agent_id?),
           tested_at (timestamp?), version (integer).
           — What every "test case" in V&V, every "acceptance test" in FDA
             design controls, every "compliance check" in structural
             engineering, and every "simulation target" in analysis planning
             actually is.
           — Every Requirement MUST have at least one TestCriterion. A
             Requirement without a TestCriterion is untestable and cannot
             contribute to release (Failure Definition item a).
           — test_method maps to the classic V-model verification methods:
             analysis (calculation), simulation (FEA/CFD), inspection (visual/
             dimensional), demonstration (functional test), test (physical
             test), similarity (comparison to qualified design).
           — Source: SRC-D007, SRC-D008, SRC-D015

TERM-D014: AnalysisResult = The recorded output of a simulation, calculation,
           or analysis, linked to a specific design version and the assumptions
           under which it was performed. Has: result_id (UUID), entity_id
           (UUID — Component/Assembly analyzed), entity_version (integer —
           specific version analyzed), analysis_type (enum: structural |
           thermal | electromagnetic | fluid | fatigue | tolerance_stackup |
           vibration | acoustic | optical | chemical | multi_physics |
           topology_optimization | drc_erc), solver (string — which tool),
           input_summary (object — key parameters: loads, boundary conditions,
           mesh density, material models), output_summary (object — key results:
           max stress, natural frequencies, temperature distribution, DRC
           violations), compute_ref (cross-substrate Reference? — link to
           COMPUTE Execution TERM-C004), content_ref (content_store_ref —
           full result data), assumptions (text[] — explicitly stated
           assumptions), limitations (text[] — known limitations of this
           analysis), convergence_confirmed (boolean — mesh convergence study
           completed), reviewed_by (agent_id?), status (enum: draft |
           reviewed | accepted | rejected | superseded), version (integer).
           — What every "FEA report," "CFD result," "DRC report," "tolerance
             analysis," "structural calculation," "energy model," and
             "docking score" actually is.
           — An AnalysisResult without convergence_confirmed: true SHOULD NOT
             be used for design decisions. Blind trust in simulation results
             is a forbidden state (see Section 11).
           — The simulation model (mesh, boundary conditions, solver settings)
             is the COMPOSITION of: Geometry (TERM-D006) + Material (TERM-D008)
             + Constraint (TERM-D010) + boundary conditions (in input_summary).
             This composition is assembled by FLOW-D003 (Submit Analysis) and
             submitted to COMPUTE as a Pipeline input. There is no separate
             "SimulationModel" primitive because the simulation model is
             always a view of existing design entities.
           — CROSS-SUBSTRATE NOTE: Links to COMPUTE Execution (TERM-C004) for
             provenance. Links to KNOWLEDGE Observation (TERM-K019) when
             analysis results inform epistemic state.
           — Source: SRC-D005, SRC-D011, ASM-D003

TERM-D015: DesignReview = A structured evaluation of a design artifact at a
           maturity gate, producing approval, conditional approval, rejection,
           or action items. Has: review_id (UUID), entity_id (UUID —
           Component/Assembly/Specification under review), entity_version
           (integer), review_type (enum: conceptual | preliminary |
           critical | test_readiness | production_readiness | first_article |
           as_built), reviewers[] (agent_id[]), status (enum: scheduled |
           in_progress | completed | canceled), outcome (enum: approved |
           conditionally_approved | rejected | deferred), conditions
           (text[]? — for conditional approval), action_items[]
           (object[] — {description, assignee, due_date, status}),
           discourse_ref (cross-substrate Reference? — link to COMMUNICATION
           Discourse), minutes_ref (content_store_ref? — recorded minutes),
           reviewed_at (timestamp), decided_by (agent_id — Design Authority).
           — What every "design review" (PDR, CDR, TRR, PRR, FAI), every
             "plan check" in architecture, every "design verification" in
             FDA DHF, and every "peer review" in engineering actually is.
           — CROSS-SUBSTRATE NOTE: DesignReview.discourse_ref links to a
             COMMUNICATION Discourse (TERM-M001) with a review-specific
             Protocol. The discourse captures the structured exchange (claims,
             challenges, resolutions); the DesignReview records the outcome.
             DESIGN owns the review record; COMMUNICATION owns the review
             discourse process.
           — Source: SRC-D007, SRC-D014, SRC-D015, SRC-D016 (67% require 2+
             cycles)
```

### Configuration & Evolution

```
TERM-D016: DesignVersion = An immutable snapshot of a design artifact at a
           point in time. Has: version_id (UUID), entity_id (UUID),
           entity_type (string — Component, Assembly, Specification, etc.),
           version_number (integer — monotonically increasing), state_snapshot
           (object — complete entity state at this version), content_ref
           (content_store_ref? — associated binary artifacts), change_summary
           (text — what changed from previous version), changed_by (agent_id),
           changed_at (timestamp), change_order_id (UUID? — ChangeOrder that
           authorized this version, if post-release), predecessor_version_id
           (UUID? — previous version), is_released (boolean).
           — What every "revision" in PLM, every "save point" in CAD history,
             every "version" in BIM model management, and every "iteration"
             in design development actually is.
           — DesignVersion is IMMUTABLE. Once created, it cannot be modified.
             New versions create new DesignVersion records. This is the physical
             design analog of immutable event history.
           — ASM-D006: Physical version control differs from software. Each
             version may have associated prototypes, tooling, test specimens,
             and regulatory submissions. Versions cannot be freely discarded.
           — Source: SRC-D004, SRC-D014, ASM-D006

TERM-D017: ChangeOrder = A formal request to modify a released design, with
           impact analysis, approval workflow, and implementation tracking.
           Has: change_order_id (UUID), title (string), description (text),
           change_type (enum: design_change | document_change | process_change |
           material_substitution | standard_update | deviation | waiver),
           affected_entities[] (object[] — {entity_type, entity_id, impact
           description}), impact_analysis (text — what other Components,
           Assemblies, Configurations, BOMs are affected), priority (enum:
           emergency | high | normal | low), status (enum: draft | submitted |
           in_review | approved | in_implementation | completed | rejected |
           canceled), requested_by (agent_id), approved_by (agent_id?),
           approval_discourse_ref (cross-substrate Reference? — COMMUNICATION
           Discourse/Consensus), implementation_deadline (timestamp?),
           cost_estimate (decimal?), version (integer).
           — What every "ECO" (Engineering Change Order), "ECN" (Engineering
             Change Notice), "RFC" (Request for Change), "variation" in
             construction, and "design amendment" in architecture actually is.
           — A ChangeOrder MUST include impact_analysis identifying ALL affected
             entities (Failure Definition item c). Impact cascades through the
             component tree and configuration dependencies.
           — CROSS-SUBSTRATE NOTE: ChangeOrder approval links to COMMUNICATION
             Commitment (TERM-M007) and Consensus (TERM-M018). The approval
             workflow IS a structured discourse about whether the change
             should proceed. COMMUNICATION owns the discourse process; DESIGN
             owns the change record.
           — Source: SRC-D004, SRC-D014, SRC-D016 (12% from material
             substitution, 23% from untested requirements)

TERM-D018: Configuration = A named, valid combination of specific Component
           and Assembly versions that together form a complete, consistent
           product. Has: configuration_id (UUID), name (string), description
           (text), baseline_type (enum: functional | allocated | product |
           as_built | as_maintained), members[] (object[] — {entity_type,
           entity_id, version_number}), validity_status (enum: valid |
           invalid | pending_validation), validation_errors (text[]? — if
           invalid), effectivity (object? — date range, serial number range,
           or lot range where this configuration applies), parent_configuration_id
           (UUID? — for configuration hierarchy), version (integer).
           — What every "configuration baseline" in CMII, every "product
             structure" in PLM, every "model version" in BIM, every "design
             freeze" in project management, and every "150% BOM" resolution
             in variant management actually is.
           — A Configuration is VALID only if all member interfaces are
             compatible, all member constraints are satisfiable simultaneously,
             and no Variant (TERM-D019) is unresolved. Validity is computed,
             not declared (Failure Definition item b).
           — Source: SRC-D004, SRC-D014

TERM-D019: Variant = A declared point of variation in a design where multiple
           valid alternatives exist. Has: variant_id (UUID), parent_entity_id
           (UUID — Assembly or Configuration containing this variant),
           variant_name (string — what varies), options[] (object[] —
           {option_name, entity_type, entity_id, conditions}), selection_rule
           (text — how to choose: by customer option, by effectivity, by
           geography, by regulatory requirement), default_option_id (UUID?),
           status (enum: open | resolved | deprecated), resolved_option_id
           (UUID? — if resolved), version (integer).
           — What every "option" in automotive configuration, every "variant"
             in product family management, every "alternative" in design
             exploration, and every "product option" in PLM actually is.
           — An unresolved Variant in a Configuration makes the Configuration
             pending_validation until the Variant is resolved.
           — Source: SRC-D004, SRC-D014
```

### Manufacturing & Fabrication

```
TERM-D020: FabricationMethod = The specification of how a Component is
           manufactured — the process, tooling, and parameters. Has:
           method_id (UUID), component_id (UUID), process_type (enum:
           machining | casting | forging | stamping | injection_molding |
           extrusion | additive | pcb_fabrication | semiconductor_fab |
           welding | brazing | soldering | assembly_manual | assembly_automated |
           chemical_synthesis | biological_culture | composite_layup |
           3d_printing | sheet_metal | construction), tooling_requirements
           (text), process_parameters (object — feeds, speeds, temperatures,
           pressures, cure times, etc.), surface_finish_achievable (string?),
           tolerance_achievable (string? — process capability), setup_time
           (duration?), cycle_time (duration?), cost_model (object? —
           fixed + variable), dfm_notes (text[] — manufacturing warnings/
           recommendations), version (integer).
           — What every "manufacturing process plan," "fabrication specification,"
             "work instruction," "synthesis route," and "construction method
             statement" actually is.
           — ASM-D004: The design-manufacturing boundary is artificial. Additive
             manufacturing has already collapsed it. FabricationMethod is a
             first-class design primitive because manufacturing feasibility IS
             a design constraint.
           — CROSS-SUBSTRATE NOTE: FabricationMethod maps to PHYSICAL Process
             (TERM-P019) when executed. DESIGN specifies how to make it;
             PHYSICAL executes the process with real equipment. The handoff:
             DESIGN FabricationMethod → PHYSICAL Process configuration.
           — Source: SRC-D010, SRC-D013, ASM-D004

TERM-D021: BillOfMaterials = A hierarchical list of all Components, Materials,
           and quantities required to produce an Assembly. Has: bom_id (UUID),
           assembly_id (UUID — the Assembly this BOM represents), bom_type
           (enum: engineering | manufacturing | service | as_built),
           line_items[] (object[] — {component_id, material_id?, quantity,
           unit, reference_designators[]?, find_number, notes}),
           total_cost_estimate (decimal?), total_mass_estimate (decimal?),
           derived_from_assembly (boolean — true if auto-derived from Assembly
           component tree), overrides (object[]? — manual modifications to
           auto-derived BOM), version (integer).
           — What every "BOM" in PLM, every "parts list" on a drawing, every
             "material takeoff" in construction, every "reagent list" in
             chemistry, and every "component list" in electronics actually is.
           — BOM types reflect the design-to-manufacturing lifecycle:
             engineering (eBOM): as-designed structure
             manufacturing (mBOM): as-built structure (may differ from eBOM
             due to manufacturing process requirements)
             service (sBOM): spare parts structure
             as_built: actual parts used (may differ from mBOM due to
             substitutions)
           — CROSS-SUBSTRATE NOTE: BOM cost data links to BUSINESS Transactions
             (TERM-008) for financial tracking. BOM quantity data feeds
             production planning (BUSINESS workflows).
           — Source: SRC-D004, SRC-D010, SRC-D014

TERM-D022: Drawing = A 2D annotated representation of a designed artifact,
           sufficient for production, inspection, or construction without
           access to the 3D model. Has: drawing_id (UUID), entity_id
           (UUID — Component or Assembly depicted), drawing_type (enum:
           detail | assembly | installation | schematic | wiring_diagram |
           p_and_id | construction | shop | as_built), views[] (object[] —
           {view_type, projection, scale, section_cuts}), dimensions[]
           (Tolerance refs — each dimension IS a Tolerance), notes[]
           (text[] — manufacturing/construction notes), title_block (object —
           drawn_by, checked_by, approved_by, dates, revision, sheet_number),
           standard_ref (Standard ref — drawing standard, e.g., ASME Y14.100),
           content_ref (content_store_ref — actual drawing file), version
           (integer).
           — What every "engineering drawing," "shop drawing," "construction
             drawing," "fabrication drawing," "schematic," and "wiring diagram"
             actually is.
           — Drawing is NOT Geometry (TERM-D006). Geometry is the 3D/abstract
             shape. Drawing is the 2D annotated production representation
             DERIVED from Geometry but enhanced with dimensions, tolerances,
             notes, surface finish symbols, and GD&T callouts that do not
             exist in the 3D model. Drawings carry legal authority in many
             jurisdictions.
           — Source: SRC-D009, SRC-D012, SRC-D008
```

### Integration & Interfaces

```
TERM-D023: Interface = A defined boundary between Components or Assemblies
           through which physical, electrical, thermal, data, or other exchange
           occurs. Has: interface_id (UUID), name (string), interface_type
           (enum: mechanical | electrical | thermal | fluid | optical | data |
           electromagnetic | chemical | structural), side_a (object —
           {entity_type, entity_id, port_description}), side_b (object —
           same), constraints[] (Constraint refs — interface compatibility
           requirements), protocol (string? — for data/electrical interfaces),
           mating_geometry (Geometry ref? — for mechanical interfaces),
           status (enum: proposed | negotiating | agreed | frozen |
           broken), controlled_by (agent_id — interface owner), version
           (integer).
           — What every "interface control document" (ICD), every "connector
             specification," every "API definition" between hardware subsystems,
             every "pipe connection" in process engineering, and every "joint
             detail" in construction actually is.
           — 18% of project delays come from interface mismatches (SRC-D016).
             Interfaces are first-class because they are where subsystem
             designs meet and where most integration failures occur.
           — Interface negotiation between subsystem teams is a structured
             process. When status is "negotiating," changes to either side
             require agreement from both.
           — CROSS-SUBSTRATE NOTE: Interface negotiation promotes to
             COMMUNICATION Discourse (TERM-M001) when formal agreement is
             required between design teams. COMMUNICATION owns the negotiation
             process; DESIGN owns the interface record.
           — Source: SRC-D007, SRC-D001, SRC-D016

TERM-D024: DesignEnvelope = The bounded authority of an AI Agent over design
           artifacts. Defines what Components, Assemblies, and design operations
           an AI agent may perform. Has: envelope_id (UUID), agent_id (UUID),
           scope (object — {component_ids[], assembly_ids[], operation_types[]:
           enum create | modify | analyze | review_assist | release_prepare}),
           material_authority (enum: approved_list_only | propose_new |
           none), geometry_authority (enum: parametric_only | topology_change |
           full | none), constraint_authority (enum: evaluate_only |
           propose_waiver | modify_non_safety | full), max_cost_impact
           (decimal? — maximum cost impact of any single design change),
           requires_human_review (boolean[] — per operation type), valid_from
           (timestamp), valid_until (timestamp), granted_by (agent_id —
           Design Authority), version (integer).
           — What every "design authority delegation," "scope of work for
             design consultants," and "AI tool permissions" actually is —
             formalized as an enforceable envelope.
           — DesignEnvelope sits in the Agent authority chain: Business Agent
             Envelope (TERM-030) → Epistemic Envelope (TERM-K022) →
             DesignEnvelope → Compute Envelope (TERM-C019) → Communicative
             Envelope (TERM-M013) → PhysicalEnvelope (TERM-P015). Effective
             authority = intersection of all applicable envelopes.
           — ASM-D005: AI agents will generate designs but MUST operate within
             bounded authority. DesignEnvelope is the mechanism.
           — CROSS-SUBSTRATE NOTE: DesignEnvelope authority MUST NOT exceed
             the base Business Agent Envelope (TERM-030) or the Epistemic
             Envelope (TERM-K022). An agent that cannot claim knowledge of
             material properties (epistemic limit) cannot design with those
             properties (design limit).
           — Source: ASM-D005, CROSS-SUBSTRATE-CONVENTIONS.md §1

TERM-D025: ParametricRelation = A declared mathematical relationship between
           design parameters that must be maintained as the design evolves.
           Has: relation_id (UUID), expression (text — mathematical expression,
           e.g., "wall_thickness >= diameter / 10"), parameters[] (object[] —
           {name, entity_type, entity_id, attribute_path, current_value, unit}),
           relation_type (enum: equality | inequality | proportional |
           conditional | lookup_table), status (enum: satisfied | violated |
           unchecked), violation_severity (enum: error | warning),
           version (integer).
           — What every "design equation," "parametric constraint," "design
             table," "spreadsheet formula driving CAD," and "engineering rule
             of thumb formalized" actually is.
           — ParametricRelations enable design automation: change one parameter,
             and all related parameters update. This is the mechanism for
             Constraint Primacy (Property D6) — constraints propagate through
             parametric relationships.
           — Source: SRC-D001, SRC-D011

TERM-D026: DesignSpace = A bounded multidimensional region of valid design
           parameter combinations. Has: space_id (UUID), entity_id (UUID —
           Component or Assembly being explored), parameters[] (object[] —
           {name, type, min, max, step?, distribution?}), constraints[]
           (Constraint refs — boundaries of the space), objectives[]
           (object[] — {name, direction: minimize | maximize, weight}),
           explored_points (integer — how many configurations evaluated),
           pareto_front (object[]? — non-dominated solutions),
           optimal_point_id (UUID? — selected design point), exploration_method
           (enum: exhaustive | random | latin_hypercube | bayesian |
           genetic | topology_optimization | gradient | manual),
           compute_pipeline_ref (cross-substrate Reference? — COMPUTE Pipeline
           running the exploration), status (enum: defined | exploring |
           explored | point_selected), version (integer).
           — What every "design of experiments," "parametric sweep," "trade
             study," "optimization problem," "generative design exploration,"
             and "what-if analysis" actually is.
           — Property D2 (Combinatorial Explosion): the design space for a
             50-parameter assembly is astronomically large. DesignSpace
             formalizes the exploration — what was explored, how, and what
             was found.
           — CROSS-SUBSTRATE NOTE: DesignSpace exploration executes via
             COMPUTE Pipelines (TERM-C010). Each explored point is a COMPUTE
             Execution. The exploration strategy may be a KNOWLEDGE Experiment
             (TERM-K017). Results inform KNOWLEDGE Propositions about the
             design space.
           — Source: SRC-D011, SRC-D005, SRC-D013
```

### System

```
TERM-D027: Event = An immutable record of something that happened within the
           design system. The append-only audit trail. Has: event_id (UUID),
           timestamp (ISO-8601), entity_type (string), entity_id (UUID),
           event_type (string — e.g., "component.created", "review.approved",
           "change_order.submitted", "constraint.violated",
           "tolerance.stack_failed", "configuration.validated"),
           actor_id (UUID), actor_type (enum: human | ai_agent | system),
           payload (object — event-specific data), trace_id (W3C traceparent),
           caused_by (event_id? — upstream event), organization_id (UUID).
           — The design-domain instantiation of the universal Event pattern
             shared by all substrates. Design-specific event_types include:
             requirement.decomposed, component.released, geometry.updated,
             material.substituted, analysis.completed, review.action_item_added,
             change_order.impact_cascaded, configuration.baseline_established,
             tolerance.stack_warning, interface.broken, bom.derived,
             design_space.exploration_completed, envelope.violation_attempted.
           — CROSS-SUBSTRATE NOTE: Design Events are emitted to the shared
             event bus per CROSS-SUBSTRATE-CONVENTIONS.md §3 on topic
             substrate.design.{entity_type}.{event_type}.
           — Source: ASM-D008, all SRC

TERM-D028: Annotation = Commentary, notes, or markup attached to any design
           entity. Has: annotation_id (UUID), entity_type (string), entity_id
           (UUID), annotation_type (enum: comment | question | action_item |
           manufacturing_note | inspection_note | markup | dimension_query |
           change_request_informal), content (text), spatial_anchor (object? —
           {geometry_id, position, orientation} for spatially-anchored
           annotations), author_id (agent_id), created_at (timestamp), status
           (enum: open | resolved | superseded), resolved_by (agent_id?),
           resolved_at (timestamp?), version (integer).
           — What every "comment" in a CAD review, every "markup" on a PDF,
             every "RFI" in construction, every "redline" on a drawing, and
             every "sticky note" on a design model actually is.
           — Annotation is DESIGN-internal commentary. When an Annotation
             requires structured response (formal approval, tracked action
             items, multi-party discussion), it promotes to a COMMUNICATION
             Speech Act (TERM-M002) within a Discourse (TERM-M001). Same
             pattern as BUSINESS Conversation (TERM-021) promoting to
             COMMUNICATION Discourse.
           — Source: SRC-D012, SRC-D016
```

---

## 4. CORE CAPABILITIES

> ~30 capabilities organized by function. Each capability references the
> primitives and assumptions that require it. MUST = mandatory for conformance.
> SHOULD = strongly recommended. MAY = optional.

### Modeling Capabilities

```
CAP-D001: The system MUST allow creation, modification, and deletion of
          Components (TERM-D004) with all declared attributes. Every Component
          MUST be linked to exactly one Specification (TERM-D002).
          — Source: TERM-D004, ASM-D001

CAP-D002: The system MUST support recursive Assembly (TERM-D005) composition —
          Assemblies containing Components and sub-Assemblies to arbitrary
          depth. The system MUST prevent circular assembly references.
          — Source: TERM-D005, ASM-D007

CAP-D003: The system MUST store Geometry (TERM-D006) for all physical
          Components, supporting at minimum the following representation_types:
          brep, mesh, parametric, 2d_profile, schematic, layout_2d. Additional
          representation_types (molecular_graph, voxel, point_cloud, implicit,
          quantum_structure) SHOULD be supported.
          — Source: TERM-D006, ASM-D003, SRC-D001, SRC-D002, SRC-D003, SRC-D006

CAP-D004: The system MUST maintain Topology (TERM-D007) independently of
          Geometry. Changes to Geometry that alter Topology MUST trigger
          Topology revalidation. Changes to Topology MUST flag potentially
          affected Geometry.
          — Source: TERM-D007, SRC-D002

CAP-D005: The system MUST support Material (TERM-D008) assignment to Components,
          including material_class, properties[], and traceability to knowledge
          source (knowledge_proposition_ref). Material substitution MUST create
          a DesignRationale (TERM-D003) record.
          — Source: TERM-D008, TERM-D003, SRC-D008

CAP-D006: The system MUST enforce ParametricRelations (TERM-D025) — when any
          parameter in a relation changes, all dependent parameters MUST be
          recomputed and all violated relations MUST be flagged immediately.
          — Source: TERM-D025, Property D6 (Constraint Primacy)

CAP-D007: The system MUST support Interface (TERM-D023) definition between
          Components/Assemblies, including all interface_types (mechanical,
          electrical, thermal, fluid, optical, data, electromagnetic, chemical,
          structural). Interface compatibility MUST be validated when either
          side changes.
          — Source: TERM-D023, SRC-D016 (18% delays from interface mismatches)

CAP-D008: The system MUST allow Annotation (TERM-D028) on any design entity,
          including spatially-anchored annotations on Geometry. Annotations
          with annotation_type: action_item MUST track resolution status.
          — Source: TERM-D028, SRC-D012
```

### Constraint & Verification Capabilities

```
CAP-D009: The system MUST support Constraint (TERM-D010) definition with all
          constraint_types and verification_methods. Constraints with
          verification_method: automated_rule_check MUST be evaluatable
          without human intervention (DRC/ERC/clash detection).
          — Source: TERM-D010, SRC-D002 (EDA DRC), SRC-D003 (BIM clash)

CAP-D010: The system MUST propagate Constraints bidirectionally through
          Assembly hierarchies. A Constraint added to a child Component that
          affects the parent Assembly MUST be surfaced at the Assembly level.
          A Constraint on an Assembly MUST be checked against all member
          Components.
          — Source: TERM-D010, Property D6 (Constraint Primacy)

CAP-D011: The system MUST support Tolerance (TERM-D011) specification with all
          tolerance_types including GD&T geometric tolerances per ASME Y14.5 /
          ISO 1101. Each Tolerance MUST include nominal_value, upper_limit,
          lower_limit, and unit at minimum.
          — Source: TERM-D011, SRC-D009

CAP-D012: The system MUST support Requirement (TERM-D001) management including
          hierarchical decomposition (parent-child), traceability to
          TestCriteria (TERM-D013), and status tracking. Every Requirement
          MUST have testable: true to be included in a released Specification.
          — Source: TERM-D001, TERM-D013, ASM-D002

CAP-D013: The system MUST enforce that every Requirement in a released
          Specification has at least one linked TestCriterion with
          result_status != untested. Release MUST be blocked if any
          Requirement lacks test evidence.
          — Source: TERM-D013, Failure Definition (a), SRC-D016

CAP-D014: The system MUST record AnalysisResults (TERM-D014) linked to specific
          design versions, with explicit assumptions, limitations, and
          convergence status. The system SHOULD warn when design changes
          invalidate existing AnalysisResults.
          — Source: TERM-D014, SRC-D005

CAP-D015: The system MUST support DesignReview (TERM-D015) workflows with
          maturity gates (conceptual, preliminary, critical, test_readiness,
          production_readiness, first_article, as_built). Review outcome MUST
          be recorded with justification.
          — Source: TERM-D015, SRC-D015

CAP-D016: The system MUST support Tolerance stack-up analysis at the Assembly
          level. Individual part tolerances that are individually valid but
          produce an assembly-level violation MUST be detected and flagged.
          Stack-up methods: worst-case, RSS, and Monte Carlo MUST be supported.
          — Source: TERM-D011, ASM-D011, SRC-D009 (31% defects from stack-up)
```

### Configuration & Change Capabilities

```
CAP-D017: The system MUST create immutable DesignVersions (TERM-D016) for every
          design entity modification. No in-place mutation of released designs.
          Version history MUST be queryable — any prior version retrievable.
          — Source: TERM-D016, ASM-D006, ASM-D008

CAP-D018: The system MUST enforce ChangeOrder (TERM-D017) workflow for any
          modification to a released design. ChangeOrders MUST include impact
          analysis identifying ALL affected Components, Assemblies,
          Configurations, and BOMs.
          — Source: TERM-D017, Failure Definition (c), SRC-D014

CAP-D019: The system MUST support Configuration (TERM-D018) management including
          baseline establishment, validity computation, and effectivity
          management (date, serial number, lot). Configuration validity MUST
          be automatically computed based on member interface compatibility
          and constraint satisfaction.
          — Source: TERM-D018, SRC-D014, Failure Definition (b)

CAP-D020: The system MUST support Variant (TERM-D019) management — declared
          points of variation with options, selection rules, and resolution
          tracking. Unresolved Variants MUST prevent Configuration validation.
          — Source: TERM-D019, SRC-D004

CAP-D021: The system MUST support Standard (TERM-D012) referencing with
          immutable version pinning. When a referenced Standard is superseded,
          the system MUST flag affected designs for review but MUST NOT
          automatically update references.
          — Source: TERM-D012, SRC-D008

CAP-D022: The system MUST record DesignRationale (TERM-D003) for all significant
          design decisions. At minimum: material selection, geometry choices
          with trade-offs, constraint waivers, and deviation from standards.
          Rationale records MUST be immutable.
          — Source: TERM-D003, ASM-D002, SRC-D016 (12% change orders from lost
            rationale)
```

### Manufacturing & Release Capabilities

```
CAP-D023: The system MUST support FabricationMethod (TERM-D020) specification
          for all physical Components, including DFM analysis linkage. The
          system SHOULD warn when design geometry is incompatible with
          specified fabrication process (e.g., undercuts for machining,
          minimum trace width for PCB, minimum wall thickness for injection
          molding).
          — Source: TERM-D020, SRC-D010, SRC-D013

CAP-D024: The system MUST support BillOfMaterials (TERM-D021) derivation from
          Assembly component trees, with support for manual overrides
          (eBOM → mBOM transformation). BOM types: engineering, manufacturing,
          service, and as_built MUST be supported.
          — Source: TERM-D021, SRC-D004

CAP-D025: The system MUST support Drawing (TERM-D022) creation with standard-
          compliant annotation (dimensions as Tolerances, GD&T callouts,
          notes, title block). Drawings MUST be traceable to source Geometry
          and SHOULD warn when source Geometry changes invalidate the Drawing.
          — Source: TERM-D022, SRC-D009, SRC-D012

CAP-D026: The system MUST enforce release gates: a design MUST NOT be released
          for manufacturing unless: (1) all Requirements have tested
          TestCriteria, (2) all mandatory DesignReviews are approved, (3)
          Configuration is valid, (4) all mandatory AnalysisResults are
          accepted, (5) BOM is complete, (6) FabricationMethod is specified.
          — Source: Failure Definition, SRC-D015

CAP-D027: The system MUST support DesignSpace (TERM-D026) definition and
          exploration tracking, including recording of all explored points,
          Pareto fronts for multi-objective optimization, and selected design
          point with rationale.
          — Source: TERM-D026, SRC-D011, Property D2 (Combinatorial Explosion)
```

### Integration Capabilities

```
CAP-D028: The system MUST emit Events (TERM-D027) to the shared event bus per
          CROSS-SUBSTRATE-CONVENTIONS.md §3 for all entity state changes.
          Event topics: substrate.design.{entity_type}.{event_type}.
          — Source: TERM-D027, ASM-D008, CROSS-SUBSTRATE-CONVENTIONS.md §3

CAP-D029: The system MUST enforce DesignEnvelope (TERM-D024) restrictions for
          all AI Agent (ACT-D004, ACT-D005) operations. Operations outside
          envelope MUST be rejected with audit log entry. Envelope violations
          MUST be reported as Events.
          — Source: TERM-D024, ASM-D005, CROSS-SUBSTRATE-CONVENTIONS.md §1

CAP-D030: The system MUST maintain the append-only Event log as the
          authoritative design history file. Events MUST NOT be modified or
          deleted. Minimum retention: 30 years for general designs; lifetime
          of artifact + 10 years for regulated products; 100+ years for
          buildings and infrastructure (ASM-D012).
          — Source: TERM-D027, ASM-D008, ASM-D012, SRC-D015

CAP-D031: The system MUST support import and export of design data in open,
          non-proprietary formats: STEP AP242 (mechanical), IFC 4.3
          (architectural), IPC-2581 (electronics), ReqIF (requirements),
          OSLC (lifecycle integration). Proprietary format import SHOULD be
          supported via adapter plugins.
          — Source: ASM-D010, ASM-D012, SRC-D001, SRC-D002, SRC-D003

CAP-D032: The system MUST support cross-substrate References per CROSS-
          SUBSTRATE-CONVENTIONS.md §5 for all integration points: Component ↔
          PhysicalAsset, Material ↔ Knowledge Proposition, AnalysisResult ↔
          Compute Execution, DesignReview ↔ Communication Discourse,
          FabricationMethod ↔ Physical Process.
          — Source: CROSS-SUBSTRATE-CONVENTIONS.md §5, all integration points
```

---

## 5. DOMAIN OBJECTS & STATE (WHAT EXISTS AND HOW IT CHANGES)

> Every primitive from Section 3 has a corresponding entity definition here. Entity
> identifiers use the ENT-D prefix. State machines use SM-D. Together they form the
> complete data model of artifact specification from first requirement through final
> fabrication instruction.

### 5.1 Intent & Requirements Entities

```
ENT-D001: Requirement — Source: TERM-D001, SRC-D007, SRC-D015
  Purpose:        An atomic, testable statement constraining the design solution space.
  Attributes:
    - requirement_id      | UUID           | globally unique, immutable       | required
    - specification_id    | ref ENT-D002   | parent Specification             | required
    - type                | enum: functional | performance | interface |
                            environmental | regulatory | safety | reliability |
                            manufacturability | cost                          | required
    - statement           | text           | natural language requirement     | required
    - rationale           | text           | why this requirement exists      | required
    - priority            | enum: shall | should | may                       | required
    - testable            | boolean        | MUST be true for release         | required  | default: false
    - parent_requirement_id | ref ENT-D001 | for decomposition hierarchy     | optional
    - version             | integer        | monotonically increasing         | required  | default: 1
    - status              | enum: draft | active | superseded | deleted      | required  | default: draft
    - test_criteria       | list<ref ENT-D013> | linked TestCriteria          | computed
    - created_by          | agent_id       | —                               | required
    - created_at          | timestamp      | —                               | required
  Identity:       UUID (globally unique, immutable)
  Lifecycle:      See SM-D001 (Requirement Lifecycle)
  Persistence:    Persistent, event-sourced
  Ownership:      ACT-D001 (Designer) or ACT-D005 (General AI within DesignEnvelope) creates.
                  ACT-D003 (Design Authority) approves status transitions.
  Relationships:  Belongs to ENT-D002 (Specification) — N:1, required
                  Parent-child decomposition — 1:N, optional (self-referencing)
                  Tested by ENT-D013 (TestCriterion) — 1:N, MUST have ≥1 for release
  Constraints:    testable must be true before Specification release.
                  Children satisfy parent: parent.status = satisfied iff all children satisfied.

ENT-D002: Specification — Source: TERM-D002, SRC-D007, SRC-D014
  Purpose:        Versioned, complete collection of Requirements, Constraints, and TestCriteria.
  Attributes:
    - specification_id    | UUID           | globally unique, immutable       | required
    - name                | string         | ≤256 chars                       | required
    - description         | text           | —                               | required
    - version             | integer        | monotonically increasing         | required  | default: 1
    - status              | enum: draft | in_review | approved | released |
                            superseded | withdrawn                           | required  | default: draft
    - artifact_type       | enum: component | assembly | system | material |
                            process                                          | required
    - domain              | enum: mechanical | electronic | architectural |
                            molecular | systems | multi_domain               | required
    - maturity_level      | enum: conceptual | preliminary | detailed |
                            released | as_built                              | required  | default: conceptual
    - requirements        | list<ref ENT-D001> | all Requirements            | computed
    - constraints         | list<ref ENT-D010> | all Constraints             | computed
    - test_criteria       | list<ref ENT-D013> | all TestCriteria            | computed
    - standards           | list<ref ENT-D012> | referenced Standards        | optional
    - created_by          | agent_id       | —                               | required
    - approved_by         | agent_id       | Design Authority                | optional
    - approved_at         | timestamp      | —                               | optional
    - organization_id     | UUID           | scoping                         | required
  Identity:       UUID (globally unique, immutable)
  Lifecycle:      See SM-D006 (Specification Lifecycle)
  Persistence:    Persistent, event-sourced
  Ownership:      ACT-D001 (Designer) creates. ACT-D003 (Design Authority) approves/releases.
  Relationships:  Contains ENT-D001 (Requirement) — 1:N
                  Contains ENT-D010 (Constraint) — 1:N
                  Contains ENT-D013 (TestCriterion) — 1:N
                  References ENT-D012 (Standard) — N:N
                  Governs ENT-D004 (Component) or ENT-D005 (Assembly) — 1:1
  Constraints:    Cannot transition to released if any Requirement has testable: false.
                  Cannot transition to released if any TestCriterion has result_status: untested.

ENT-D003: DesignRationale — Source: TERM-D003, SRC-D013, ASM-D002
  Purpose:        Immutable record of why a design decision was made.
  Attributes:
    - rationale_id        | UUID           | globally unique, immutable       | required
    - entity_type         | string         | what entity this applies to      | required
    - entity_id           | UUID           | —                               | required
    - decision            | text           | what was decided                 | required
    - alternatives_considered | list<text> | what else was evaluated          | required  | ≥1
    - selection_criteria   | text          | why this alternative chosen      | required
    - evidence_refs       | list<cross-substrate Reference> | KNOWLEDGE links | optional
    - trade_offs          | text           | what was sacrificed              | optional
    - constraints_active  | list<ref ENT-D010> | driving constraints          | optional
    - decided_by          | agent_id       | —                               | required
    - decided_at          | timestamp      | —                               | required
  Identity:       UUID (globally unique, immutable)
  Lifecycle:      IMMUTABLE once created. Superseded by new DesignRationale via ChangeOrder.
  Persistence:    Persistent, append-only, immutable
  Ownership:      Any authorized actor creates. System owns once persisted.
  Relationships:  Attached to any design entity — N:1
                  References KNOWLEDGE Arguments (TERM-K015) via evidence_refs
  Constraints:    alternatives_considered MUST have ≥1 entry. A decision with no
                  alternatives considered is not a design decision.
```

### 5.2 Structure & Geometry Entities

```
ENT-D004: Component — Source: TERM-D004, SRC-D001, SRC-D004
  Purpose:        Atomic unit of design composition — independently specified, manufactured, tested.
  Attributes:
    - component_id        | UUID           | globally unique, immutable       | required
    - name                | string         | ≤256 chars                       | required
    - part_number         | string         | organization-scoped              | required
    - specification_id    | ref ENT-D002   | governing Specification          | required
    - geometry_id         | ref ENT-D006   | physical shape                   | optional (required for physical)
    - material_id         | ref ENT-D008   | fabrication material             | optional (required for physical)
    - current_version     | integer        | —                               | required  | default: 1
    - status              | enum: concept | in_design | in_review | released |
                            production | obsolete                            | required  | default: concept
    - domain              | enum: mechanical | electronic | architectural |
                            molecular | software_hardware | multi_domain     | required
    - parent_assembly_id  | ref ENT-D005   | if part of Assembly              | optional
    - fabrication_method_id | ref ENT-D020 | how to make it                  | optional
    - mass                | decimal        | in kg                            | optional
    - cost_estimate       | decimal        | in org currency                  | optional
    - organization_id     | UUID           | scoping                         | required
  Identity:       UUID (globally unique, immutable)
  Lifecycle:      See SM-D002 (Component Lifecycle)
  Persistence:    Persistent, event-sourced
  Ownership:      ACT-D001 (Designer) or ACT-D004/D005 (AI within DesignEnvelope) creates.
                  ACT-D003 (Design Authority) approves release.
  Relationships:  Governed by ENT-D002 (Specification) — N:1, required
                  Belongs to ENT-D005 (Assembly) — N:1, optional
                  Has ENT-D006 (Geometry) — 1:1, optional
                  Has ENT-D008 (Material) — N:1, optional
                  Has ENT-D020 (FabricationMethod) — 1:1, optional
                  Connected via ENT-D023 (Interface) — N:N
                  Has ENT-D016 (DesignVersion) history — 1:N
  Constraints:    part_number unique within organization.
                  Physical Components MUST have geometry_id and material_id before release.

ENT-D005: Assembly — Source: TERM-D005, SRC-D001, SRC-D004
  Purpose:        Composed structure of Components with spatial relationships and interfaces.
  Attributes:
    - assembly_id         | UUID           | globally unique, immutable       | required
    - name                | string         | ≤256 chars                       | required
    - assembly_number     | string         | organization-scoped              | required
    - specification_id    | ref ENT-D002   | governing Specification          | required
    - components          | list<object>   | {component_id, quantity, position,
                            orientation, reference_designator}               | required  | ≥1
    - sub_assemblies      | list<ref ENT-D005> | recursive                   | optional
    - interfaces          | list<ref ENT-D023> | connections between members | optional
    - geometry_id         | ref ENT-D006   | assembly-level envelope/model    | optional
    - configuration_id    | ref ENT-D018   | valid version combination        | optional
    - current_version     | integer        | —                               | required  | default: 1
    - status              | enum: concept | in_design | in_review | released |
                            production | obsolete                            | required  | default: concept
    - bom_id              | ref ENT-D021   | derived BillOfMaterials          | optional
    - organization_id     | UUID           | scoping                         | required
  Identity:       UUID (globally unique, immutable)
  Lifecycle:      Same as Component (SM-D002)
  Persistence:    Persistent, event-sourced
  Ownership:      ACT-D001 (Designer) creates. ACT-D003 (Design Authority) approves release.
  Relationships:  Contains ENT-D004 (Component) — 1:N, ≥1
                  Contains ENT-D005 (Assembly) — 1:N, optional (recursive)
                  Has ENT-D023 (Interface) connections — 1:N
                  Has ENT-D021 (BillOfMaterials) — 1:1, derivable
                  Has ENT-D018 (Configuration) — 1:N
  Constraints:    No circular references (Assembly cannot contain itself at any depth).
                  components list MUST have ≥1 entry.

ENT-D006: Geometry — Source: TERM-D006, SRC-D001, SRC-D002, SRC-D003
  Purpose:        Representation-independent description of physical shape and spatial extent.
  Attributes:
    - geometry_id         | UUID           | globally unique, immutable       | required
    - entity_id           | UUID           | Component or Assembly            | required
    - representation_type | enum: brep | mesh | parametric | implicit |
                            point_cloud | 2d_profile | schematic | layout_2d |
                            molecular_graph | voxel | quantum_structure      | required
    - coordinate_system   | enum: cartesian | cylindrical | spherical |
                            fractional_crystal | internal_molecular          | required
    - units               | enum: m | mm | um | nm | angstrom | mil | inch  | required
    - bounding_box        | object         | {min_x, min_y, min_z, max_x,
                            max_y, max_z} in declared units                  | required
    - content_ref         | content_store_ref | actual geometry data          | required
    - content_hash        | SHA-256        | integrity verification           | required
    - parameter_count     | integer        | for parametric representations   | optional
    - face_count          | integer        | for brep/mesh                    | optional
    - version             | integer        | —                               | required  | default: 1
  Identity:       UUID (globally unique, immutable)
  Lifecycle:      Immutable per version. New version = new Geometry entity.
  Persistence:    Metadata persistent. Binary data in Content Store (DEP-D003).
  Ownership:      Created by ACT-D001 (Designer) or ACT-D004/D005 (AI within DesignEnvelope).
  Relationships:  Describes ENT-D004 (Component) or ENT-D005 (Assembly) — N:1
  Constraints:    content_hash MUST match stored content. Mismatch = integrity violation.
                  bounding_box must be valid (min < max in all axes).

ENT-D007: Topology — Source: TERM-D007, SRC-D002, SRC-D007
  Purpose:        Abstract connectivity between Components independent of geometry.
  Attributes:
    - topology_id         | UUID           | globally unique                  | required
    - assembly_id         | ref ENT-D005   | parent Assembly                  | required
    - nodes               | list<object>   | {entity_type, entity_id}         | required  | ≥2
    - edges               | list<object>   | {interface_id, from_node, to_node} | required  | ≥1
    - topology_type       | enum: spatial | electrical | thermal | fluid |
                            structural | signal | power | logical            | required
    - constraints         | list<ref ENT-D010> | topological constraints     | optional
    - version             | integer        | —                               | required  | default: 1
  Identity:       UUID (globally unique)
  Lifecycle:      Versioned. Updated when Assembly structure changes.
  Persistence:    Persistent, event-sourced
  Ownership:      Derived from Assembly structure or explicitly defined by ACT-D001 (Designer).
  Relationships:  Belongs to ENT-D005 (Assembly) — N:1
                  Nodes reference ENT-D004/D005. Edges reference ENT-D023 (Interface).
  Constraints:    Graph must be connected (no isolated nodes) or explicitly declared disconnected.
                  No self-loops (node cannot interface with itself).
```

### 5.3 Material Entities

```
ENT-D008: Material — Source: TERM-D008, SRC-D008, SRC-D010
  Purpose:        Characterized substance from which Components are fabricated.
  Attributes:
    - material_id         | UUID           | globally unique                  | required
    - name                | string         | ≤256 chars                       | required
    - designation         | string         | standard designation             | required
    - material_class      | enum: metal | polymer | ceramic | composite |
                            semiconductor | biological | chemical | glass |
                            wood | natural_fiber | metamaterial              | required
    - properties          | list<ref ENT-D009> | MaterialProperties          | required  | ≥1
    - standards           | list<ref ENT-D012> | material specifications     | optional
    - data_source         | enum: tested | literature | simulation | estimated | required
    - knowledge_proposition_ref | cross-substrate Reference | KNOWLEDGE link | optional
    - organization_id     | UUID           | scoping                         | required
  Identity:       UUID (globally unique)
  Lifecycle:      Active → Deprecated (when superseded by better data or removed from approved list)
  Persistence:    Persistent
  Ownership:      ACT-D001 (Designer) or ACT-D002 (Engineer) creates. Organization manages.
  Relationships:  Used by ENT-D004 (Component) — 1:N
                  Has ENT-D009 (MaterialProperty) — 1:N, ≥1
                  References ENT-D012 (Standard) — N:N
  Constraints:    properties list MUST have ≥1 entry. Material without properties is unusable.

ENT-D009: MaterialProperty — Source: TERM-D009, SRC-D008, SRC-D009
  Purpose:        Measurable characteristic of a Material under specified conditions.
  Attributes:
    - property_id         | UUID           | globally unique                  | required
    - material_id         | ref ENT-D008   | parent Material                  | required
    - property_type       | enum: mechanical | thermal | electrical | optical |
                            magnetic | chemical | biological | acoustic |
                            density | cost                                   | required
    - property_name       | string         | e.g., "yield_strength"           | required
    - value               | decimal        | —                               | required
    - unit                | string         | SI unit                          | required
    - conditions          | object         | {temperature, pressure, strain_rate,
                            frequency, humidity, etc.}                        | required
    - uncertainty         | decimal        | measurement uncertainty          | optional
    - source              | enum: tested | published | simulated | interpolated | required
    - test_method         | string         | e.g., "ASTM E8"                 | optional
    - confidence          | decimal        | from KNOWLEDGE (0.0-1.0)        | optional
    - valid_range         | object         | {temp_min, temp_max, etc.}       | optional
  Identity:       UUID (globally unique)
  Lifecycle:      Immutable per version. Updated via new records with provenance.
  Persistence:    Persistent
  Ownership:      Created by ACT-D002 (Engineer) or imported from DEP-D009.
  Relationships:  Belongs to ENT-D008 (Material) — N:1
  Constraints:    conditions MUST be specified. Bare property values without conditions are invalid.
```

### 5.4 Constraint & Standards Entities

```
ENT-D010: Constraint — Source: TERM-D010, SRC-D001, SRC-D008
  Purpose:        Formal limitation restricting the design space.
  Attributes:
    - constraint_id       | UUID           | globally unique                  | required
    - entity_id           | UUID           | what this constrains             | required
    - entity_type         | string         | —                               | required
    - constraint_type     | enum: dimensional | geometric | structural |
                            thermal | electrical | electromagnetic | chemical |
                            regulatory | cost | mass | power | manufacturing |
                            interface | environmental | safety               | required
    - expression          | text           | formal expression (machine-
                            parseable for automated_rule_check)              | required
    - verification_method | enum: manual_inspection | analysis | simulation |
                            automated_rule_check | demonstration |
                            certification | test                             | required
    - severity            | enum: mandatory | preferred | guidance           | required
    - status              | enum: active | waived | superseded               | required  | default: active
    - waiver_justification | text          | required if status: waived       | conditional
    - source_description  | string         | Requirement, Standard, or physics | required
    - version             | integer        | —                               | required  | default: 1
  Identity:       UUID (globally unique)
  Lifecycle:      Active → Waived (with justification) → Superseded
  Persistence:    Persistent, event-sourced
  Ownership:      Created by ACT-D001/D002 (Designer/Engineer). Waivers require ACT-D003.
  Relationships:  Constrains any design entity — N:1
                  Part of ENT-D002 (Specification) — N:1, optional
                  May reference ENT-D012 (Standard) as source
  Constraints:    Waiver requires justification and Design Authority approval.
                  Constraints with verification_method: automated_rule_check MUST have
                  machine-parseable expression.

ENT-D011: Tolerance — Source: TERM-D011, SRC-D009, ASM-D011
  Purpose:        Permissible variation in a dimension, property, or behavior.
  Attributes:
    - tolerance_id        | UUID           | globally unique                  | required
    - entity_id           | UUID           | Component or Assembly            | required
    - tolerance_type      | enum: dimensional | geometric_form |
                            geometric_orientation | geometric_location |
                            geometric_runout | geometric_profile |
                            surface_finish | position_true | statistical |
                            material_property | performance                  | required
    - nominal_value       | decimal        | —                               | required
    - upper_limit         | decimal        | —                               | required
    - lower_limit         | decimal        | —                               | required
    - unit                | string         | —                               | required
    - datum_refs          | list<string>   | GD&T datum features              | optional
    - material_condition  | enum: mmc | lmc | rfs | none                    | required  | default: none
    - statistical_model   | enum: normal | uniform | beta | empirical | none | required  | default: none
    - cpk_target          | decimal        | process capability target        | optional
    - stack_analysis_id   | UUID           | assembly-level stack-up ref      | optional
    - version             | integer        | —                               | required  | default: 1
  Identity:       UUID (globally unique)
  Lifecycle:      Active → Superseded (via ChangeOrder)
  Persistence:    Persistent
  Ownership:      Created by ACT-D001 (Designer) or ACT-D002 (Engineer).
  Relationships:  Applies to ENT-D004 (Component) or ENT-D005 (Assembly) — N:1
                  Referenced by ENT-D022 (Drawing) dimensions
  Constraints:    lower_limit ≤ nominal_value ≤ upper_limit.
                  GD&T types MUST specify datum_refs per ASME Y14.5.

ENT-D012: Standard — Source: TERM-D012, SRC-D008, SRC-D015
  Purpose:        Referenced external normative document constraining the design.
  Attributes:
    - standard_id         | UUID           | globally unique                  | required
    - designation         | string         | e.g., "ASME Y14.5-2018"         | required
    - issuing_body        | string         | e.g., "ASME"                    | required
    - title               | string         | —                               | required
    - version_string      | string         | edition/year                     | required
    - effective_date      | date           | —                               | required
    - status              | enum: current | superseded | withdrawn           | required
    - scope               | text           | what the standard covers         | required
    - clauses_referenced  | list<string>   | specific sections used           | optional
    - content_ref         | content_store_ref | full text if licensed         | optional
    - superseded_by       | ref ENT-D012   | if superseded                    | optional
  Identity:       UUID (globally unique)
  Lifecycle:      Current → Superseded (by issuing body) → Withdrawn
  Persistence:    Persistent, immutable once referenced
  Ownership:      System imports. Organization curates referenced standards library.
  Relationships:  Referenced by ENT-D002 (Specification) — N:N
                  Referenced by ENT-D008 (Material) — N:N
                  Referenced by ENT-D010 (Constraint) as source — 1:N
  Constraints:    IMMUTABLE once referenced by a released design. Supersession tracked
                  but existing references preserved.
```

### 5.5 Verification & Validation Entities

```
ENT-D013: TestCriterion — Source: TERM-D013, SRC-D007, SRC-D015
  Purpose:        Formal condition determining whether a Requirement is satisfied.
  Attributes:
    - criterion_id        | UUID           | globally unique                  | required
    - requirement_id      | ref ENT-D001   | tested Requirement               | required
    - description         | text           | what is being tested             | required
    - test_method         | enum: analysis | simulation | inspection |
                            demonstration | test | similarity               | required
    - acceptance_condition | text          | pass/fail criteria               | required
    - result_value        | decimal        | measured/computed value           | optional
    - result_status       | enum: untested | pass | fail | inconclusive     | required  | default: untested
    - result_evidence_ref | cross-substrate Reference | AnalysisResult or
                            PHYSICAL Measurement                             | optional
    - tested_by           | agent_id       | —                               | optional
    - tested_at           | timestamp      | —                               | optional
    - version             | integer        | —                               | required  | default: 1
  Identity:       UUID (globally unique)
  Lifecycle:      untested → pass | fail | inconclusive (may retest)
  Persistence:    Persistent, event-sourced
  Ownership:      Created by ACT-D001/D002 (Designer/Engineer). Results by ACT-D002 or system.
  Relationships:  Tests ENT-D001 (Requirement) — N:1, required
                  May reference ENT-D014 (AnalysisResult) as evidence
  Constraints:    Every Requirement MUST have ≥1 TestCriterion for release.

ENT-D014: AnalysisResult — Source: TERM-D014, SRC-D005, ASM-D003
  Purpose:        Recorded output of simulation/calculation linked to design version.
  Attributes:
    - result_id           | UUID           | globally unique                  | required
    - entity_id           | UUID           | Component/Assembly analyzed      | required
    - entity_version      | integer        | specific version analyzed        | required
    - analysis_type       | enum: structural | thermal | electromagnetic |
                            fluid | fatigue | tolerance_stackup | vibration |
                            acoustic | optical | chemical | multi_physics |
                            topology_optimization | drc_erc                  | required
    - solver              | string         | which tool                       | required
    - input_summary       | object         | key parameters (loads, BCs, mesh) | required
    - output_summary      | object         | key results                      | required
    - compute_ref         | cross-substrate Reference | COMPUTE Execution    | optional
    - content_ref         | content_store_ref | full result data              | required
    - assumptions         | list<text>     | explicitly stated                | required  | ≥1
    - limitations         | list<text>     | known limitations                | optional
    - convergence_confirmed | boolean      | mesh convergence study done      | required  | default: false
    - reviewed_by         | agent_id       | —                               | optional
    - status              | enum: draft | reviewed | accepted | rejected |
                            superseded                                       | required  | default: draft
    - version             | integer        | —                               | required  | default: 1
  Identity:       UUID (globally unique)
  Lifecycle:      draft → reviewed → accepted | rejected | superseded
  Persistence:    Persistent, event-sourced. Results immutable once accepted.
  Ownership:      Created by ACT-D002 (Engineer) or system (via COMPUTE). Reviewed by ACT-D002.
  Relationships:  Analyzes ENT-D004/D005 at specific version — N:1
                  May reference COMPUTE Execution (TERM-C004)
                  Used as evidence by ENT-D013 (TestCriterion)
  Constraints:    assumptions MUST have ≥1 entry. Analysis without stated assumptions
                  cannot be reviewed. convergence_confirmed SHOULD be true for acceptance.

ENT-D015: DesignReview — Source: TERM-D015, SRC-D007, SRC-D015
  Purpose:        Structured evaluation at a maturity gate with recorded outcome.
  Attributes:
    - review_id           | UUID           | globally unique                  | required
    - entity_id           | UUID           | artifact under review            | required
    - entity_version      | integer        | specific version reviewed        | required
    - review_type         | enum: conceptual | preliminary | critical |
                            test_readiness | production_readiness |
                            first_article | as_built                         | required
    - reviewers           | list<agent_id> | —                               | required  | ≥1
    - status              | enum: scheduled | in_progress | completed |
                            canceled                                         | required  | default: scheduled
    - outcome             | enum: approved | conditionally_approved |
                            rejected | deferred                              | optional (set on completion)
    - conditions          | list<text>     | for conditional approval         | optional
    - action_items        | list<object>   | {description, assignee, due_date,
                            status: open | closed}                           | optional
    - discourse_ref       | cross-substrate Reference | COMMUNICATION Discourse | optional
    - minutes_ref         | content_store_ref | recorded minutes             | optional
    - reviewed_at         | timestamp      | completion time                  | optional
    - decided_by          | agent_id       | Design Authority                 | optional
  Identity:       UUID (globally unique)
  Lifecycle:      See SM-D004 (DesignReview Lifecycle)
  Persistence:    Persistent, event-sourced
  Ownership:      Created by ACT-D001/D002. Decided by ACT-D003 (Design Authority).
  Relationships:  Reviews ENT-D004/D005/D002 at specific version — N:1
                  Links to COMMUNICATION Discourse via discourse_ref
  Constraints:    outcome requires decided_by (Design Authority).
                  conditionally_approved requires ≥1 condition.
```

### 5.6 Configuration & Evolution Entities

```
ENT-D016: DesignVersion — Source: TERM-D016, SRC-D004, ASM-D006
  Purpose:        Immutable snapshot of a design artifact at a point in time.
  Attributes:
    - version_id          | UUID           | globally unique, immutable       | required
    - entity_id           | UUID           | —                               | required
    - entity_type         | string         | —                               | required
    - version_number      | integer        | monotonically increasing         | required
    - state_snapshot      | object         | complete entity state            | required
    - content_ref         | content_store_ref | associated binary artifacts  | optional
    - change_summary      | text           | what changed                     | required
    - changed_by          | agent_id       | —                               | required
    - changed_at          | timestamp      | —                               | required
    - change_order_id     | ref ENT-D017   | if post-release change           | optional
    - predecessor_version_id | ref ENT-D016 | previous version               | optional
    - is_released         | boolean        | —                               | required  | default: false
  Identity:       UUID (globally unique, immutable)
  Lifecycle:      IMMUTABLE once created. No modification. No deletion.
  Persistence:    Persistent, append-only, immutable
  Ownership:      System creates on entity modification.
  Relationships:  Snapshots any design entity — N:1
                  Chain: predecessor_version_id → previous version
  Constraints:    version_number monotonically increasing per entity.
                  state_snapshot MUST be complete (reconstructable without external state).

ENT-D017: ChangeOrder — Source: TERM-D017, SRC-D004, SRC-D014
  Purpose:        Formal request to modify a released design with impact analysis and approval.
  Attributes:
    - change_order_id     | UUID           | globally unique                  | required
    - title               | string         | ≤256 chars                       | required
    - description         | text           | —                               | required
    - change_type         | enum: design_change | document_change |
                            process_change | material_substitution |
                            standard_update | deviation | waiver             | required
    - affected_entities   | list<object>   | {entity_type, entity_id,
                            impact_description}                              | required  | ≥1
    - impact_analysis     | text           | cascading impact description     | required
    - priority            | enum: emergency | high | normal | low            | required  | default: normal
    - status              | enum: draft | submitted | in_review | approved |
                            in_implementation | completed | rejected |
                            canceled                                         | required  | default: draft
    - requested_by        | agent_id       | —                               | required
    - approved_by         | agent_id       | Design Authority                 | optional
    - approval_discourse_ref | cross-substrate Reference | COMMUNICATION    | optional
    - implementation_deadline | timestamp  | —                               | optional
    - cost_estimate       | decimal        | —                               | optional
    - version             | integer        | —                               | required  | default: 1
  Identity:       UUID (globally unique)
  Lifecycle:      See SM-D003 (ChangeOrder Lifecycle)
  Persistence:    Persistent, event-sourced
  Ownership:      Any authorized actor creates. ACT-D003 (Design Authority) approves.
  Relationships:  Affects ENT-D004/D005/D002/D018 — N:N
                  Links to COMMUNICATION Discourse for approval workflow
                  Produces ENT-D016 (DesignVersion) on implementation
  Constraints:    impact_analysis MUST identify ALL affected entities (Failure Def c).
                  affected_entities MUST have ≥1 entry.
                  Post-release changes MUST go through ChangeOrder (CAP-D018).

ENT-D018: Configuration — Source: TERM-D018, SRC-D004, SRC-D014
  Purpose:        Named, valid combination of specific Component/Assembly versions.
  Attributes:
    - configuration_id    | UUID           | globally unique                  | required
    - name                | string         | ≤256 chars                       | required
    - description         | text           | —                               | optional
    - baseline_type       | enum: functional | allocated | product |
                            as_built | as_maintained                         | required
    - members             | list<object>   | {entity_type, entity_id,
                            version_number}                                  | required  | ≥1
    - validity_status     | enum: valid | invalid | pending_validation       | required  | default: pending_validation
    - validation_errors   | list<text>     | if invalid                       | optional
    - effectivity         | object         | {date_range?, serial_range?,
                            lot_range?}                                      | optional
    - parent_configuration_id | ref ENT-D018 | hierarchy                     | optional
    - version             | integer        | —                               | required  | default: 1
  Identity:       UUID (globally unique)
  Lifecycle:      See SM-D005 (Configuration Lifecycle)
  Persistence:    Persistent, event-sourced
  Ownership:      ACT-D001/D002 creates. System computes validity.
  Relationships:  Contains versioned ENT-D004/D005 — N:N
                  May contain unresolved ENT-D019 (Variant) — N:N
  Constraints:    validity_status computed, not declared. Valid only if all member
                  interfaces compatible and all constraints satisfiable simultaneously.
                  Unresolved Variants → pending_validation.

ENT-D019: Variant — Source: TERM-D019, SRC-D004
  Purpose:        Declared point of variation where multiple valid alternatives exist.
  Attributes:
    - variant_id          | UUID           | globally unique                  | required
    - parent_entity_id    | UUID           | Assembly or Configuration        | required
    - variant_name        | string         | what varies                      | required
    - options             | list<object>   | {option_name, entity_type,
                            entity_id, conditions}                           | required  | ≥2
    - selection_rule      | text           | how to choose                    | required
    - default_option_id   | UUID           | —                               | optional
    - status              | enum: open | resolved | deprecated               | required  | default: open
    - resolved_option_id  | UUID           | if resolved                      | optional
    - version             | integer        | —                               | required  | default: 1
  Identity:       UUID (globally unique)
  Lifecycle:      open → resolved | deprecated
  Persistence:    Persistent
  Ownership:      ACT-D001 (Designer) creates. Resolution by ACT-D001/D003.
  Relationships:  Belongs to ENT-D005 (Assembly) or ENT-D018 (Configuration) — N:1
  Constraints:    options MUST have ≥2 entries (a variant with one option is not a variant).
                  resolved requires resolved_option_id.
```

### 5.7 Manufacturing Entities

```
ENT-D020: FabricationMethod — Source: TERM-D020, SRC-D010, ASM-D004
  Purpose:        Specification of how a Component is manufactured.
  Attributes:
    - method_id           | UUID           | globally unique                  | required
    - component_id        | ref ENT-D004   | —                               | required
    - process_type        | enum: machining | casting | forging | stamping |
                            injection_molding | extrusion | additive |
                            pcb_fabrication | semiconductor_fab | welding |
                            brazing | soldering | assembly_manual |
                            assembly_automated | chemical_synthesis |
                            biological_culture | composite_layup |
                            3d_printing | sheet_metal | construction         | required
    - tooling_requirements | text          | —                               | optional
    - process_parameters  | object         | feeds, speeds, temperatures, etc. | optional
    - surface_finish_achievable | string   | —                               | optional
    - tolerance_achievable | string        | process capability               | optional
    - setup_time          | duration       | —                               | optional
    - cycle_time          | duration       | —                               | optional
    - cost_model          | object         | fixed + variable                 | optional
    - dfm_notes           | list<text>     | manufacturing warnings           | optional
    - version             | integer        | —                               | required  | default: 1
  Identity:       UUID (globally unique)
  Lifecycle:      Versioned. Updated via ChangeOrder when process changes.
  Persistence:    Persistent
  Ownership:      ACT-D001/D002 creates. Manufacturing engineering validates.
  Relationships:  Describes ENT-D004 (Component) — N:1
                  Maps to PHYSICAL Process (TERM-P019) when executed
  Constraints:    process_type must be compatible with Component's material and geometry.

ENT-D021: BillOfMaterials — Source: TERM-D021, SRC-D004, SRC-D010
  Purpose:        Hierarchical list of Components, Materials, and quantities for production.
  Attributes:
    - bom_id              | UUID           | globally unique                  | required
    - assembly_id         | ref ENT-D005   | —                               | required
    - bom_type            | enum: engineering | manufacturing | service |
                            as_built                                         | required
    - line_items          | list<object>   | {component_id, material_id?,
                            quantity, unit, reference_designators[], find_number,
                            notes}                                           | required  | ≥1
    - total_cost_estimate | decimal        | —                               | optional
    - total_mass_estimate | decimal        | —                               | optional
    - derived_from_assembly | boolean      | auto-derived from component tree | required
    - overrides           | list<object>   | manual modifications             | optional
    - version             | integer        | —                               | required  | default: 1
  Identity:       UUID (globally unique)
  Lifecycle:      Derived → Reviewed → Released (with parent Assembly)
  Persistence:    Persistent
  Ownership:      System derives from Assembly. ACT-D001/D002 may override.
  Relationships:  Represents ENT-D005 (Assembly) — N:1
                  Contains ENT-D004 (Component) references — 1:N
                  Links to BUSINESS Transactions for cost tracking
  Constraints:    line_items MUST have ≥1 entry.
                  If derived_from_assembly: true, overrides tracked separately.

ENT-D022: Drawing — Source: TERM-D022, SRC-D009, SRC-D012
  Purpose:        2D annotated representation sufficient for production.
  Attributes:
    - drawing_id          | UUID           | globally unique                  | required
    - entity_id           | UUID           | Component or Assembly depicted   | required
    - drawing_type        | enum: detail | assembly | installation |
                            schematic | wiring_diagram | p_and_id |
                            construction | shop | as_built                   | required
    - views               | list<object>   | {view_type, projection, scale,
                            section_cuts}                                    | required  | ≥1
    - dimensions          | list<ref ENT-D011> | each dimension IS a Tolerance | optional
    - notes               | list<text>     | manufacturing/construction notes | optional
    - title_block         | object         | {drawn_by, checked_by, approved_by,
                            dates, revision, sheet_number}                   | required
    - standard_ref        | ref ENT-D012   | drawing standard                 | required
    - content_ref         | content_store_ref | actual drawing file           | required
    - version             | integer        | —                               | required  | default: 1
  Identity:       UUID (globally unique)
  Lifecycle:      Draft → Checked → Approved → Released
  Persistence:    Persistent. Content in Content Store.
  Ownership:      ACT-D001 (Designer) creates. Checked by peer. Approved by ACT-D003.
  Relationships:  Depicts ENT-D004/D005 — N:1
                  References ENT-D011 (Tolerance) for dimensions — 1:N
                  References ENT-D012 (Standard) for drawing standard — N:1
  Constraints:    title_block MUST include drawn_by, approved_by, revision.
                  Drawing SHOULD warn when source Geometry changes (CAP-D025).
```

### 5.8 Integration Entities

```
ENT-D023: Interface — Source: TERM-D023, SRC-D007, SRC-D016
  Purpose:        Defined boundary between Components through which exchange occurs.
  Attributes:
    - interface_id        | UUID           | globally unique                  | required
    - name                | string         | ≤256 chars                       | required
    - interface_type      | enum: mechanical | electrical | thermal | fluid |
                            optical | data | electromagnetic | chemical |
                            structural                                       | required
    - side_a              | object         | {entity_type, entity_id,
                            port_description}                                | required
    - side_b              | object         | same                             | required
    - constraints         | list<ref ENT-D010> | compatibility requirements  | optional
    - protocol            | string         | for data/electrical interfaces   | optional
    - mating_geometry     | ref ENT-D006   | for mechanical interfaces        | optional
    - status              | enum: proposed | negotiating | agreed | frozen |
                            broken                                           | required  | default: proposed
    - controlled_by       | agent_id       | interface owner                  | required
    - version             | integer        | —                               | required  | default: 1
  Identity:       UUID (globally unique)
  Lifecycle:      proposed → negotiating → agreed → frozen. broken if violated.
  Persistence:    Persistent, event-sourced
  Ownership:      Controlled_by agent manages. Both sides must agree for frozen status.
  Relationships:  Connects two ENT-D004/D005 entities — N:N
                  Part of ENT-D007 (Topology) edges — N:1
  Constraints:    side_a ≠ side_b (no self-interfaces).
                  Changes while status: frozen require ChangeOrder.

ENT-D024: DesignEnvelope — Source: TERM-D024, ASM-D005, CROSS-SUBSTRATE-CONVENTIONS §1
  Purpose:        Bounded AI Agent authority over design artifacts.
  Attributes:
    - envelope_id         | UUID           | globally unique                  | required
    - agent_id            | UUID           | —                               | required
    - scope               | object         | {component_ids[], assembly_ids[],
                            operation_types[]: create | modify | analyze |
                            review_assist | release_prepare}                 | required
    - material_authority  | enum: approved_list_only | propose_new | none    | required
    - geometry_authority  | enum: parametric_only | topology_change | full |
                            none                                             | required
    - constraint_authority | enum: evaluate_only | propose_waiver |
                            modify_non_safety | full                         | required
    - max_cost_impact     | decimal        | maximum per change               | optional
    - requires_human_review | list<boolean> | per operation type              | required
    - valid_from          | timestamp      | —                               | required
    - valid_until         | timestamp      | —                               | required
    - granted_by          | agent_id       | Design Authority                 | required
    - version             | integer        | —                               | required  | default: 1
  Identity:       UUID (globally unique)
  Lifecycle:      Active (within valid_from/valid_until) → Expired → Revoked
  Persistence:    Persistent, event-sourced
  Ownership:      Granted by ACT-D003 (Design Authority). Enforced by system.
  Relationships:  Scopes ACT-D004/D005 (AI Agents) — 1:1
                  Chained from BUSINESS Agent Envelope (TERM-030) and
                  KNOWLEDGE Epistemic Envelope (TERM-K022)
  Constraints:    Authority MUST NOT exceed base Business Agent Envelope.
                  Authority MUST NOT exceed Epistemic Envelope.
                  valid_until MUST be > valid_from. Auto-expires.

ENT-D025: ParametricRelation — Source: TERM-D025, SRC-D001, SRC-D011
  Purpose:        Mathematical relationship between design parameters.
  Attributes:
    - relation_id         | UUID           | globally unique                  | required
    - expression          | text           | mathematical expression          | required
    - parameters          | list<object>   | {name, entity_type, entity_id,
                            attribute_path, current_value, unit}             | required  | ≥2
    - relation_type       | enum: equality | inequality | proportional |
                            conditional | lookup_table                       | required
    - status              | enum: satisfied | violated | unchecked           | required  | default: unchecked
    - violation_severity  | enum: error | warning                            | required
    - version             | integer        | —                               | required  | default: 1
  Identity:       UUID (globally unique)
  Lifecycle:      Active. Re-evaluated on any parameter change.
  Persistence:    Persistent
  Ownership:      ACT-D001 (Designer) creates.
  Relationships:  Links parameters across design entities — N:N
  Constraints:    parameters MUST have ≥2 entries (a relation needs ≥2 parameters).
                  status automatically recomputed on parameter change.

ENT-D026: DesignSpace — Source: TERM-D026, SRC-D011, SRC-D005
  Purpose:        Bounded multidimensional region of valid design parameter combinations.
  Attributes:
    - space_id            | UUID           | globally unique                  | required
    - entity_id           | UUID           | Component/Assembly being explored | required
    - parameters          | list<object>   | {name, type, min, max, step?,
                            distribution?}                                   | required  | ≥1
    - constraints         | list<ref ENT-D010> | space boundaries            | optional
    - objectives          | list<object>   | {name, direction: minimize |
                            maximize, weight}                                | required  | ≥1
    - explored_points     | integer        | —                               | required  | default: 0
    - pareto_front        | list<object>   | non-dominated solutions          | optional
    - optimal_point_id    | UUID           | selected design point            | optional
    - exploration_method  | enum: exhaustive | random | latin_hypercube |
                            bayesian | genetic | topology_optimization |
                            gradient | manual                                | required
    - compute_pipeline_ref | cross-substrate Reference | COMPUTE Pipeline   | optional
    - status              | enum: defined | exploring | explored |
                            point_selected                                   | required  | default: defined
    - version             | integer        | —                               | required  | default: 1
  Identity:       UUID (globally unique)
  Lifecycle:      defined → exploring → explored → point_selected
  Persistence:    Persistent, event-sourced
  Ownership:      ACT-D001/D002/D005 creates. Exploration via COMPUTE.
  Relationships:  Explores ENT-D004/D005 — N:1
                  Executed via COMPUTE Pipeline (TERM-C010)
  Constraints:    objectives MUST have ≥1 entry.
                  point_selected requires optimal_point_id.
```

### 5.9 System Entities

```
ENT-D027: Event — Source: TERM-D027, ASM-D008
  Purpose:        Immutable record of design system occurrence.
  Attributes:
    - event_id            | UUID           | globally unique, immutable       | required
    - timestamp           | ISO-8601       | when it happened                 | required
    - entity_type         | string         | —                               | required
    - entity_id           | UUID           | —                               | required
    - event_type          | string         | e.g., "component.released"       | required
    - actor_id            | UUID           | —                               | required
    - actor_type          | enum: human | ai_agent | system                  | required
    - payload             | object         | event-specific data              | required
    - trace_id            | W3C traceparent | —                              | required
    - caused_by           | ref ENT-D027   | upstream event                   | optional
    - organization_id     | UUID           | scoping                         | required
  Identity:       UUID (globally unique, immutable)
  Lifecycle:      IMMUTABLE. No modification. No deletion.
  Persistence:    Append-only. Minimum 30 years general; lifetime + 10 years regulated;
                  100+ years buildings/infrastructure (ASM-D012).
  Ownership:      System. No actor may modify or delete Events.
  Relationships:  Causal chain via caused_by — 1:1, optional
  Constraints:    Events MUST NOT be modified or deleted (CAP-D030).

ENT-D028: Annotation — Source: TERM-D028, SRC-D012
  Purpose:        Commentary, notes, or markup attached to any design entity.
  Attributes:
    - annotation_id       | UUID           | globally unique                  | required
    - entity_type         | string         | —                               | required
    - entity_id           | UUID           | —                               | required
    - annotation_type     | enum: comment | question | action_item |
                            manufacturing_note | inspection_note | markup |
                            dimension_query | change_request_informal        | required
    - content             | text           | —                               | required
    - spatial_anchor      | object         | {geometry_id, position,
                            orientation}                                     | optional
    - author_id           | agent_id       | —                               | required
    - created_at          | timestamp      | —                               | required
    - status              | enum: open | resolved | superseded               | required  | default: open
    - resolved_by         | agent_id       | —                               | optional
    - resolved_at         | timestamp      | —                               | optional
    - version             | integer        | —                               | required  | default: 1
  Identity:       UUID (globally unique)
  Lifecycle:      open → resolved | superseded
  Persistence:    Persistent
  Ownership:      Any authorized actor creates. Resolved by assignee or author.
  Relationships:  Attached to any design entity — N:1
                  May promote to COMMUNICATION Speech Act (TERM-M002)
  Constraints:    action_item type MUST track resolution status (CAP-D008).
```

### 5.10 State Machines

```
SM-D001: Requirement Lifecycle — Entity: ENT-D001
  States: draft → active → superseded → deleted
  Transitions:
    draft → active:        Requirement validated as testable, approved for inclusion
                           Guard: testable = true
                           Action: emit requirement.activated Event
    active → superseded:   Replaced by new Requirement via ChangeOrder
                           Guard: replacement_requirement_id provided
                           Action: emit requirement.superseded Event
    active → deleted:      Removed (design scope reduction)
                           Guard: no active TestCriteria reference this requirement
                           Action: emit requirement.deleted Event
    draft → deleted:       Discarded before activation
                           Action: emit requirement.deleted Event

SM-D002: Component Lifecycle — Entity: ENT-D004, ENT-D005 (shared)
  States: concept → in_design → in_review → released → production → obsolete
  Transitions:
    concept → in_design:   Design work begins
                           Guard: specification_id assigned
                           Action: emit component.design_started Event
    in_design → in_review: Design submitted for review
                           Guard: all mandatory attributes populated, geometry exists
                           (for physical components)
                           Action: create DesignReview, emit component.submitted Event
    in_review → in_design: Review rejected — rework required
                           Guard: DesignReview.outcome = rejected
                           Action: emit component.rework_required Event
    in_review → released:  Review approved — design frozen
                           Guard: DesignReview.outcome = approved, all Requirements
                           have tested TestCriteria, Configuration valid (if in Assembly)
                           Action: create immutable DesignVersion, emit component.released Event
    released → production: Manufacturing has begun
                           Guard: BOM complete, FabricationMethod specified, all release
                           gates passed (CAP-D026)
                           Action: emit component.production_started Event
    released → in_design:  Post-release change via ChangeOrder
                           Guard: ChangeOrder.status = approved
                           Action: create new version, emit component.change_initiated Event
    production → obsolete: End of production life
                           Guard: authorized by Design Authority
                           Action: emit component.obsoleted Event

SM-D003: ChangeOrder Lifecycle — Entity: ENT-D017
  States: draft → submitted → in_review → approved → in_implementation → completed
          (also: rejected, canceled from multiple states)
  Transitions:
    draft → submitted:     Change request formalized
                           Guard: impact_analysis complete, affected_entities populated
                           Action: emit change_order.submitted Event
    submitted → in_review: Review process initiated
                           Guard: reviewers assigned
                           Action: create COMMUNICATION Discourse (if configured),
                           emit change_order.review_started Event
    in_review → approved:  Change authorized
                           Guard: Design Authority approval
                           Action: emit change_order.approved Event
    in_review → rejected:  Change denied
                           Guard: Design Authority rejection with justification
                           Action: emit change_order.rejected Event
    approved → in_implementation: Work begins on implementing the change
                           Action: emit change_order.implementation_started Event
    in_implementation → completed: All affected entities updated
                           Guard: all affected_entities have new DesignVersions
                           Action: emit change_order.completed Event
    * → canceled:          Withdrawn by requestor
                           Guard: not yet in_implementation
                           Action: emit change_order.canceled Event

SM-D004: DesignReview Lifecycle — Entity: ENT-D015
  States: scheduled → in_progress → completed (also: canceled)
  Transitions:
    scheduled → in_progress: Review session begins
                           Guard: all reviewers confirmed, review package available
                           Action: create COMMUNICATION Discourse (if configured),
                           emit review.started Event
    in_progress → completed: Review conclusion reached
                           Guard: outcome decided by Design Authority
                           Action: record outcome and action_items,
                           emit review.completed Event
    scheduled → canceled:  Review no longer needed
                           Action: emit review.canceled Event
    in_progress → canceled: Review abandoned (e.g., design fundamentally changed)
                           Action: emit review.canceled Event

SM-D005: Configuration Lifecycle — Entity: ENT-D018
  States: pending_validation → valid → invalid → baselined → superseded
  Transitions:
    pending_validation → valid: All members compatible, all constraints satisfied,
                           no unresolved Variants
                           Guard: system validation passes
                           Action: emit configuration.validated Event
    pending_validation → invalid: Validation fails
                           Guard: system validation fails (interface mismatch,
                           constraint conflict, unresolved variant)
                           Action: record validation_errors,
                           emit configuration.validation_failed Event
    invalid → pending_validation: Members updated, revalidation triggered
                           Action: emit configuration.revalidation_triggered Event
    valid → baselined:     Configuration frozen as baseline
                           Guard: Design Authority approval
                           Action: emit configuration.baselined Event
    valid → invalid:       Member changed, invalidating configuration
                           Guard: member version updated
                           Action: emit configuration.invalidated Event
    baselined → superseded: New baseline established
                           Guard: new Configuration baselined for same scope
                           Action: emit configuration.superseded Event

SM-D006: Specification Lifecycle — Entity: ENT-D002
  States: draft → in_review → approved → released → superseded → withdrawn
  Transitions:
    draft → in_review:     Specification submitted for review
                           Guard: ≥1 Requirement, all Requirements testable
                           Action: emit specification.submitted Event
    in_review → draft:     Review returns for rework
                           Guard: DesignReview.outcome = rejected
                           Action: emit specification.rework_required Event
    in_review → approved:  Review passes
                           Guard: DesignReview.outcome = approved
                           Action: emit specification.approved Event
    approved → released:   Released for implementation
                           Guard: all TestCriteria have result_status ≠ untested,
                           all mandatory DesignReviews completed, Design Authority sign-off
                           Action: create immutable DesignVersion,
                           emit specification.released Event
    released → superseded: Replaced by new version
                           Guard: new Specification released for same scope
                           Action: emit specification.superseded Event
    released → withdrawn:  Specification withdrawn from use
                           Guard: Design Authority authorization
                           Action: emit specification.withdrawn Event
```

---

## 6. INTERFACES (HOW ACTORS INTERACT)

> One interface per major capability cluster. Each interface specifies auth,
> request/response schemas, error codes, idempotency, and rate limits.

```
IFC-D001: Requirement Management — Implements: CAP-D012, CAP-D013 — Source: TERM-D001
  Purpose:          CRUD for Requirements with decomposition and traceability.
  Auth requirement:  ACT-D001/D005 (Designer/AI) for create/modify. ACT-D003 for approve.
  Sub-interfaces:
    IFC-D001a: Create Requirement
      Request: { specification_id, type, statement, rationale, priority, parent_requirement_id? }
      Response: { requirement_id, status: draft }
    IFC-D001b: Decompose Requirement
      Request: { parent_requirement_id, children: list<Requirement> }
      Response: { child_ids[], parent_updated }
    IFC-D001c: Query Requirements
      Request: { specification_id, filters: {type, priority, status, testable}, pagination }
      Response: { requirements: list<Requirement>, traceability_summary }
    IFC-D001d: Traceability Report
      Request: { specification_id }
      Response: { matrix: requirement → test_criteria → result_status }
  Errors:          ERR-D001 (validation), ERR-D002 (authorization), ERR-D003 (not found)
  Idempotency:     Create: keyed on specification_id + statement hash. Update: keyed on version.

IFC-D002: Component Design — Implements: CAP-D001, CAP-D005, CAP-D007 — Source: TERM-D004
  Purpose:          Create and modify Components with geometry, material, and interfaces.
  Auth requirement:  ACT-D001/D004/D005 for create/modify (AI within DesignEnvelope).
                    ACT-D003 for release approval.
  Sub-interfaces:
    IFC-D002a: Create Component
      Request: { name, part_number, specification_id, domain, material_id?, geometry? }
      Response: { component_id, status: concept }
    IFC-D002b: Update Geometry
      Request: { component_id, geometry: {representation_type, content, units} }
      Response: { geometry_id, version, content_hash, invalidated_analyses[] }
    IFC-D002c: Assign Material
      Request: { component_id, material_id, rationale }
      Response: { updated, rationale_id, knowledge_confidence? }
    IFC-D002d: Submit for Review
      Request: { component_id }
      Response: { review_id, status: scheduled, missing_prerequisites[]? }
  Errors:          ERR-D001 (validation), ERR-D002 (auth), ERR-D003 (not found),
                   ERR-D004 (envelope violation), ERR-D005 (geometry invalid),
                   ERR-D006 (prerequisites not met)
  Idempotency:     Keyed on component_id + version.

IFC-D003: Assembly Management — Implements: CAP-D002, CAP-D010, CAP-D016 — Source: TERM-D005
  Purpose:          Compose Assemblies, manage interfaces, compute tolerance stacks.
  Auth requirement:  ACT-D001/D004/D005 for create/modify. ACT-D003 for release.
  Sub-interfaces:
    IFC-D003a: Create Assembly
      Request: { name, assembly_number, specification_id, initial_components[] }
      Response: { assembly_id, topology_id, status: concept }
    IFC-D003b: Add/Remove Component
      Request: { assembly_id, action: add | remove, component_id, quantity?,
                 position?, orientation? }
      Response: { updated_component_list, topology_updated, constraint_check_result }
    IFC-D003c: Define Interface
      Request: { assembly_id, side_a, side_b, interface_type, constraints[] }
      Response: { interface_id, compatibility_check_result }
    IFC-D003d: Compute Tolerance Stack
      Request: { assembly_id, stack_method: worst_case | rss | monte_carlo,
                 iterations? (for monte_carlo) }
      Response: { stack_result, pass_fail, critical_contributors[], cpk_estimate? }
  Errors:          ERR-D001, ERR-D002, ERR-D003, ERR-D007 (circular reference),
                   ERR-D008 (interface incompatible), ERR-D009 (tolerance stack failure)
  Idempotency:     Keyed on assembly_id + version.

IFC-D004: Constraint & Analysis — Implements: CAP-D009, CAP-D014 — Source: TERM-D010, TERM-D014
  Purpose:          Define constraints, execute DRC, submit and retrieve analysis results.
  Auth requirement:  ACT-D001/D002/D004/D005 for constraints. ACT-D002 for analysis review.
  Sub-interfaces:
    IFC-D004a: Define Constraint
      Request: { entity_id, entity_type, constraint_type, expression,
                 verification_method, severity }
      Response: { constraint_id, evaluation_result (if automated_rule_check) }
    IFC-D004b: Run Automated Checks (DRC/ERC/Clash)
      Request: { entity_id, check_scope: all | specific_constraint_ids[] }
      Response: { results: list<{constraint_id, status, violations[]}>,
                 pass_count, fail_count }
    IFC-D004c: Submit Analysis
      Request: { entity_id, entity_version, analysis_type, solver,
                 input_summary, assumptions[] }
      Response: { result_id, compute_job_ref?, status: draft }
    IFC-D004d: Record Analysis Result
      Request: { result_id, output_summary, content_ref, convergence_confirmed,
                 limitations[] }
      Response: { updated, status: draft }
  Errors:          ERR-D001, ERR-D002, ERR-D003, ERR-D010 (constraint expression
                   parse error), ERR-D011 (solver unavailable — COMPUTE dependency)

IFC-D005: Configuration & Change Management — Implements: CAP-D017–D022 — Source: TERM-D016–D019
  Purpose:          Version control, change orders, configuration baselines, variants.
  Auth requirement:  ACT-D001/D002 for version/config. ACT-D003 for change order approval.
  Sub-interfaces:
    IFC-D005a: Create ChangeOrder
      Request: { title, description, change_type, affected_entities[],
                 impact_analysis, priority }
      Response: { change_order_id, status: draft }
    IFC-D005b: Approve/Reject ChangeOrder
      Request: { change_order_id, decision: approve | reject, justification }
      Response: { new_status, discourse_ref? }
    IFC-D005c: Establish Configuration Baseline
      Request: { name, baseline_type, members[], effectivity? }
      Response: { configuration_id, validity_status, validation_errors[]? }
    IFC-D005d: Resolve Variant
      Request: { variant_id, selected_option_id }
      Response: { resolved, configuration_revalidation_triggered }
    IFC-D005e: Query Version History
      Request: { entity_type, entity_id, version_range? }
      Response: { versions: list<DesignVersion>, change_orders[] }
  Errors:          ERR-D001, ERR-D002, ERR-D003, ERR-D012 (impact analysis
                   incomplete), ERR-D013 (configuration invalid)

IFC-D006: Manufacturing Release — Implements: CAP-D023–D026 — Source: TERM-D020–D022
  Purpose:          Manage fabrication methods, BOMs, drawings, and release gates.
  Auth requirement:  ACT-D001/D002 for create. ACT-D003 for release approval.
  Sub-interfaces:
    IFC-D006a: Define FabricationMethod
      Request: { component_id, process_type, tooling_requirements?,
                 process_parameters?, dfm_notes[]? }
      Response: { method_id, compatibility_warnings[]? }
    IFC-D006b: Derive BOM
      Request: { assembly_id, bom_type }
      Response: { bom_id, line_items[], total_cost?, total_mass? }
    IFC-D006c: Create Drawing
      Request: { entity_id, drawing_type, views[], standard_ref, content }
      Response: { drawing_id, title_block }
    IFC-D006d: Release Gate Check
      Request: { entity_id }
      Response: { gate_status: pass | fail, checklist: list<{gate_item,
                 status, blocking}> }
  Errors:          ERR-D001, ERR-D002, ERR-D003, ERR-D006 (prerequisites not met),
                   ERR-D014 (DFM incompatibility warning)

IFC-D007: Design Space Exploration — Implements: CAP-D027 — Source: TERM-D026
  Purpose:          Define, execute, and analyze design space explorations.
  Auth requirement:  ACT-D001/D002/D005 for define/execute. ACT-D003 for point selection.
  Sub-interfaces:
    IFC-D007a: Define DesignSpace
      Request: { entity_id, parameters[], constraints[], objectives[],
                 exploration_method }
      Response: { space_id, status: defined }
    IFC-D007b: Execute Exploration
      Request: { space_id, max_iterations?, compute_budget? }
      Response: { status: exploring, compute_pipeline_ref }
    IFC-D007c: Query Results
      Request: { space_id, filters?, pagination }
      Response: { explored_points, pareto_front?, best_per_objective[] }
    IFC-D007d: Select Design Point
      Request: { space_id, point_id, rationale }
      Response: { status: point_selected, rationale_id }
  Errors:          ERR-D001, ERR-D002, ERR-D011 (COMPUTE unavailable),
                   ERR-D015 (budget exceeded)

IFC-D008: DesignReview Workflow — Implements: CAP-D015 — Source: TERM-D015
  Purpose:          Schedule, conduct, and record design reviews.
  Auth requirement:  ACT-D001/D002 for schedule. ACT-D003 for decide outcome.
  Sub-interfaces:
    IFC-D008a: Schedule Review
      Request: { entity_id, entity_version, review_type, reviewers[] }
      Response: { review_id, status: scheduled }
    IFC-D008b: Start Review
      Request: { review_id }
      Response: { status: in_progress, discourse_ref? }
    IFC-D008c: Record Outcome
      Request: { review_id, outcome, conditions[]?, action_items[]?,
                 decided_by }
      Response: { status: completed, entity_status_updated }
  Errors:          ERR-D001, ERR-D002, ERR-D003, ERR-D006 (review package
                   incomplete)

IFC-D009: Import/Export — Implements: CAP-D031 — Source: ASM-D010, ASM-D012
  Purpose:          Import from and export to external design formats.
  Auth requirement:  ACT-D001/D002/D006 (External System validated per TRUST-D001).
  Sub-interfaces:
    IFC-D009a: Import Design Data
      Request: { format: step_ap242 | ifc_4_3 | ipc_2581 | reqif | oslc |
                 gdsii | edif, content_ref, target_scope }
      Response: { import_id, entities_created[], warnings[], errors[] }
    IFC-D009b: Export Design Data
      Request: { entity_ids[], format, include_metadata: boolean }
      Response: { export_id, content_ref, entity_count }
    IFC-D009c: Validate Import
      Request: { import_id }
      Response: { validation_result, topology_valid, geometry_valid,
                 missing_references[] }
  Errors:          ERR-D001, ERR-D016 (format not supported), ERR-D017
                   (import validation failed), ERR-D018 (geometry topology invalid)

IFC-D010: Annotation & Markup — Implements: CAP-D008 — Source: TERM-D028
  Purpose:          Create, resolve, and query annotations on design entities.
  Auth requirement:  Any authorized actor.
  Sub-interfaces:
    IFC-D010a: Create Annotation
      Request: { entity_type, entity_id, annotation_type, content,
                 spatial_anchor? }
      Response: { annotation_id, status: open }
    IFC-D010b: Resolve Annotation
      Request: { annotation_id, resolution_note }
      Response: { status: resolved }
    IFC-D010c: Query Annotations
      Request: { entity_id?, author_id?, status_filter?, annotation_type? }
      Response: { annotations: list<Annotation>, open_count, action_item_count }
  Errors:          ERR-D001, ERR-D002, ERR-D003
```

---

## 7. DATA FLOWS (HOW DATA MOVES)

> One flow per major capability cluster. Each flow is testable end-to-end.

```
FLOW-D001: Create and Release Component — Implements: CAP-D001, CAP-D013, CAP-D026
  Trigger:          Designer creates new Component
  Inputs:           Component attributes, Specification, Geometry, Material
  Steps:
    1. Create Component entity (status: concept)
    2. Assign Specification (link to ENT-D002)
    3. Define/import Geometry (store in Content Store, create ENT-D006)
    4. Assign Material (create DesignRationale for selection)
    5. Define Constraints and Tolerances (ENT-D010, ENT-D011)
    6. Transition to in_design (SM-D002)
    7. Execute automated Constraint checks (DRC/clash if applicable)
    8. Submit analysis requests to COMPUTE (via FLOW-D003)
    9. Record AnalysisResults linked to current version
    10. Submit for review (transition to in_review)
    11. Conduct DesignReview (SM-D004 → COMMUNICATION Discourse if configured)
    12. If rejected: return to in_design (step 6), rework
    13. If approved: verify all Requirements have tested TestCriteria
    14. Verify Configuration valid (if in Assembly)
    15. Create immutable DesignVersion (ENT-D016)
    16. Transition to released (SM-D002)
    17. Emit substrate.design.component.released Event
  Outputs:          Released Component with complete audit trail
  Atomicity:        Steps 15-17 MUST succeed or fail together.
  Error paths:
    Step 7: Constraint violations → block progress, report violations
    Step 13: Untested Requirements → block release (Failure Def a)
    Step 14: Invalid Configuration → block release (Failure Def b)

FLOW-D002: Change Released Design — Implements: CAP-D017, CAP-D018
  Trigger:          Need to modify a released design
  Inputs:           Change description, affected entity IDs
  Steps:
    1. Create ChangeOrder (status: draft)
    2. Populate affected_entities with ALL impacted items
    3. Perform impact analysis (cascade through Assemblies, Configurations, BOMs)
    4. Submit ChangeOrder (draft → submitted)
    5. Assign reviewers, initiate review (submitted → in_review)
    6. Create COMMUNICATION Discourse for approval workflow
    7. Design Authority approves or rejects (in_review → approved | rejected)
    8. If approved: transition affected entities to in_design via ChangeOrder
    9. Implement changes (modify entities, create new DesignVersions)
    10. Re-run affected analyses
    11. Re-validate affected Configurations
    12. ChangeOrder completed (in_implementation → completed)
    13. Emit substrate.design.change_order.completed Event
  Outputs:          Updated entities with new versions, complete change record
  Atomicity:        Steps 4 (submit) and 12 (complete) are atomic with Events.
  Error paths:
    Step 3: Impact analysis incomplete → ERR-D012, block submission
    Step 7: Rejected → record justification, notify requestor
    Step 11: Configuration invalid after change → flag, may require further changes

FLOW-D003: Submit Analysis to COMPUTE — Implements: CAP-D014 — Cross-substrate
  Trigger:          Engineer requests analysis (FEA, CFD, DRC, tolerance stack-up)
  Inputs:           Entity ID + version, analysis type, solver preference
  Steps:
    1. Collect design data: Geometry + Material + Constraints + boundary conditions
    2. Package as COMPUTE Pipeline input (CROSS-SUBSTRATE-CONVENTIONS §5 reference)
    3. Submit to COMPUTE via INT-D003 (analysis submission)
    4. Create AnalysisResult entity (status: draft, compute_ref linked)
    5. COMPUTE executes solver (this is COMPUTE's responsibility)
    6. Receive results via cross-substrate event (compute.execution.completed)
    7. Record output_summary and content_ref in AnalysisResult
    8. Engineer reviews: confirms convergence, checks assumptions
    9. AnalysisResult transitions to reviewed → accepted | rejected
    10. If accepted: link to TestCriterion as evidence
    11. Emit substrate.design.analysis.completed Event
  Outputs:          AnalysisResult linked to design version and TestCriteria
  Cross-substrate:  COMPUTE owns execution (steps 5-6). DESIGN owns packaging (1-3)
                    and consumption (7-10). Boundary = simulation request document.
  Error paths:
    Step 3: COMPUTE unavailable → queue, ERR-D011
    Step 6: Computation failed → AnalysisResult status: failed, notify engineer
    Step 8: Convergence not confirmed → warn, block acceptance for safety-critical

FLOW-D004: Design Review Process — Implements: CAP-D015 — Cross-substrate
  Trigger:          Design entity submitted for review
  Inputs:           Entity ID + version, review type, reviewer list
  Steps:
    1. Schedule DesignReview (SM-D004: scheduled)
    2. Prepare review package (entity + Specification + analysis results +
       Constraint check results + traceability matrix)
    3. Start review (scheduled → in_progress)
    4. Create COMMUNICATION Discourse with review Protocol (if configured)
    5. Reviewers examine artifacts, raise comments (→ Annotations or Speech Acts)
    6. Design team responds to comments, provides clarifications
    7. Design Authority decides outcome (approved | conditionally_approved |
       rejected | deferred)
    8. Record outcome and action_items (in_progress → completed)
    9. If conditionally_approved: track condition satisfaction
    10. Update entity status per review outcome
    11. Emit substrate.design.review.completed Event
  Outputs:          Review record with outcome, action items, discourse reference
  Cross-substrate:  COMMUNICATION owns discourse process (step 4-6). DESIGN owns
                    review record and outcome (step 7-8).

FLOW-D005: Derive BOM from Assembly — Implements: CAP-D024
  Trigger:          Assembly structure complete or modified
  Inputs:           Assembly ID
  Steps:
    1. Traverse Assembly component tree recursively
    2. Collect all Components with quantities, accounting for sub-assemblies
    3. Resolve reference_designators (if electronic domain)
    4. Calculate find_numbers per drawing convention
    5. Look up material costs from Material entities and BUSINESS cost data
    6. Calculate total_cost_estimate and total_mass_estimate
    7. Create BillOfMaterials entity (bom_type: engineering, derived_from_assembly: true)
    8. If mBOM required: allow overrides for manufacturing process needs
    9. Emit substrate.design.bom.derived Event
  Outputs:          BillOfMaterials entity linked to Assembly
  Error paths:
    Step 1: Circular reference → ERR-D007 (should never happen — prevented at Assembly creation)
    Step 5: Material cost unavailable → estimate as zero, flag warning

FLOW-D006: Configuration Validation — Implements: CAP-D019
  Trigger:          Configuration created or member updated
  Inputs:           Configuration ID with member list
  Steps:
    1. Retrieve all member entity versions
    2. Check all Interfaces between members for compatibility
    3. Check all cross-member Constraints for satisfiability
    4. Check all Variants for resolution status
    5. Check tolerance stack-ups at assembly boundaries
    6. If all pass: validity_status = valid
    7. If any fail: validity_status = invalid, record validation_errors
    8. Emit substrate.design.configuration.validated | validation_failed Event
  Outputs:          Configuration with computed validity_status
  Error paths:
    Step 2: Interface incompatible → record which interface, which constraint
    Step 3: Constraint conflict → record conflicting constraints
    Step 4: Unresolved Variant → list unresolved variants
    Step 5: Stack-up failure → report critical contributors (Failure Def d)

FLOW-D007: DesignEnvelope Enforcement — Implements: CAP-D029
  Trigger:          AI Agent (ACT-D004/D005) attempts any design operation
  Inputs:           Agent ID, operation type, target entity
  Steps:
    1. Retrieve agent's DesignEnvelope (ENT-D024)
    2. Check valid_from/valid_until (expired → reject)
    3. Check target entity against scope.component_ids/assembly_ids
    4. Check operation against scope.operation_types
    5. Check material authority (if material operation)
    6. Check geometry authority (if geometry operation)
    7. Check constraint authority (if constraint operation)
    8. Check cost impact against max_cost_impact (if applicable)
    9. Check requires_human_review for this operation type
    10. If all pass: allow operation, log in Event
    11. If any fail: reject with specific violation, log in Event
    12. Emit substrate.design.envelope.check_result Event
  Outputs:          Allow or reject with audit trail
  Error paths:
    Step 2: Expired envelope → ERR-D004, suggest renewal
    Step 3-8: Scope violation → ERR-D004 with specific violation description
    Step 9: Human review required → queue for human, do not execute

FLOW-D008: Import External Design Data — Implements: CAP-D031
  Trigger:          External system submits design data
  Inputs:           Format identifier, content reference
  Steps:
    1. Validate format (STEP AP242, IFC 4.3, IPC-2581, ReqIF, GDSII, EDIF)
    2. Parse content according to format schema
    3. Map external entities to DESIGN primitives (Component, Assembly, Material, etc.)
    4. Validate geometry topology (watertight, no self-intersections for solids)
    5. Validate requirement testability (for ReqIF imports)
    6. Detect and resolve naming conflicts with existing entities
    7. Create DESIGN entities with provenance (imported_from, import_timestamp)
    8. Store binary geometry data in Content Store
    9. Run automated Constraint checks on imported data
    10. Report: entities_created, warnings (e.g., unmapped attributes), errors
    11. Emit substrate.design.import.completed Event
  Outputs:          Imported design entities with provenance and validation report
  Error paths:
    Step 1: Unsupported format → ERR-D016
    Step 4: Invalid geometry → ERR-D018, partial import with flagged entities
    Step 6: Naming conflict → warn, prefix with import source identifier
```

---

## 8. INTEGRATION CONTRACTS (CROSS-SUBSTRATE)

> One contract per dependent substrate plus Content Store. Each contract specifies
> the protocol, auth, integration points with ownership boundaries per P1-P4,
> events emitted/consumed, failure modes, and retry policies.

```
INT-D001: BUSINESS Integration — Depends on: DEP-D004 — Source: CROSS-SUBSTRATE-CONVENTIONS
  Protocol:        Cross-substrate event bus + reference resolution
  Auth:            Mutual substrate identity per CROSS-SUBSTRATE-CONVENTIONS §1
  Integration points:
    a) Component ↔ Business Entity
       — DESIGN: owns technical specification (Component attributes, Geometry, Material)
       — BUSINESS: owns organizational tracking (project assignment, cost center, location)
       — Mapping: ENT-D004.component_id referenced by BUSINESS Entity (TERM-003)
       — Principle: P3 (BUSINESS defines organizational context, DESIGN defines technical content)
    b) BillOfMaterials ↔ Business Transaction
       — DESIGN: owns BOM structure and quantities
       — BUSINESS: owns financial tracking (purchase orders, cost rollup)
       — Mapping: ENT-D021 cost data feeds BUSINESS Transaction (TERM-008)
       — Principle: P3
    c) ChangeOrder ↔ Business Workflow
       — DESIGN: owns change technical content and impact analysis
       — BUSINESS: owns workflow routing, schedule impact, resource allocation
       — Mapping: ENT-D017 may trigger BUSINESS Workflow
       — Principle: P2 (DESIGN triggers, BUSINESS routes)
    d) DesignReview ↔ Business Schedule
       — DESIGN: owns review content and outcome
       — BUSINESS: owns scheduling and resource booking
       — Principle: P3
    e) Specification ↔ Business Document
       — DESIGN: owns technical content
       — BUSINESS: owns document management metadata (retention, access control)
       — Principle: P4 (DESIGN owns specification, BUSINESS references)
    f) DesignEnvelope ↔ Business Agent Envelope
       — DESIGN: owns design-specific authority bounds
       — BUSINESS: owns base agent identity and authority
       — DesignEnvelope authority ≤ Business Agent Envelope authority
       — Principle: P3
  Events emitted:   substrate.design.component.released,
                    substrate.design.change_order.completed,
                    substrate.design.bom.derived,
                    substrate.design.review.completed
  Events consumed:  substrate.business.organization.created,
                    substrate.business.organization.suspended,
                    substrate.business.workflow.completed,
                    substrate.business.entity.cost_updated
  Failure modes:    BUSINESS unavailable → design operations continue. Business
                    cross-references (cost, schedule) unresolvable. New agent auth blocked.
  Retry policy:     Event emission: max 10 retries, exponential backoff, DLQ.

INT-D002: KNOWLEDGE Integration — Depends on: DEP-D005 — Source: CROSS-SUBSTRATE-CONVENTIONS
  Protocol:        Cross-substrate event bus + reference resolution
  Auth:            Mutual substrate identity
  Integration points:
    a) MaterialProperty ↔ Knowledge Proposition + Confidence
       — DESIGN: consumes material property values, records which values used in decisions
       — KNOWLEDGE: owns material property truth (Proposition with confidence)
       — Boundary: KNOWLEDGE owns truth. DESIGN consumes and cites.
       — If design testing contradicts: DESIGN emits event; KNOWLEDGE evaluates.
       — Principle: P1 (KNOWLEDGE = content of knowledge, DESIGN = application)
    b) DesignRationale ↔ Knowledge Argument + Evidence
       — DESIGN: owns design-specific rationale records
       — KNOWLEDGE: owns structured argumentation and evidence provenance
       — Mapping: ENT-D003.evidence_refs → KNOWLEDGE Argument (TERM-K015)
       — Principle: P1
    c) AnalysisResult ↔ Knowledge Observation
       — DESIGN: owns analysis results as design verification evidence
       — KNOWLEDGE: may consume results as empirical observations
       — Principle: P4 (DESIGN owns result, KNOWLEDGE may reference)
    d) Constraint ↔ Knowledge Proposition
       — DESIGN: owns design constraint application
       — KNOWLEDGE: owns the scientific basis (e.g., "max operating temp of PLA is 60°C")
       — Principle: P1
    e) Standard ↔ Knowledge Source
       — DESIGN: references standards as constraints
       — KNOWLEDGE: registers standards as authoritative Sources (TERM-K020)
       — Principle: P4
    f) DesignSpace ↔ Knowledge Hypothesis + Experiment
       — DESIGN: owns design space definition and exploration tracking
       — KNOWLEDGE: may model exploration as experiment with hypothesis
       — Principle: P1
  Events emitted:   substrate.design.material.property_discrepancy,
                    substrate.design.analysis.completed,
                    substrate.design.rationale.recorded
  Events consumed:  substrate.knowledge.proposition.confidence_changed,
                    substrate.knowledge.proposition.retracted,
                    substrate.knowledge.source.reliability_changed
  Failure modes:    KNOWLEDGE unavailable → cached material data used. Confidence
                    updates not received. Designs flagged with stale-data warning.
  Retry policy:     Event emission: max 10 retries, exponential backoff, DLQ.

INT-D003: COMPUTE Integration — Depends on: DEP-D006 — Source: CROSS-SUBSTRATE-CONVENTIONS
  Protocol:        Cross-substrate event bus + direct API for computation requests
  Auth:            Mutual substrate identity + COMPUTE resource authorization
  Integration points:
    a) Analysis ↔ Compute Execution + Result
       — DESIGN: owns "what to simulate" (Geometry + Material + Constraints +
         boundary conditions = simulation request)
       — COMPUTE: owns "how to simulate" (solver, resources, scheduling)
       — Boundary: simulation request document. DESIGN assembles inputs; COMPUTE executes.
       — Mapping: ENT-D014.compute_ref → COMPUTE Execution (TERM-C004)
       — Principle: P1 (DESIGN = simulation intent, COMPUTE = execution)
    b) DesignSpace exploration ↔ Compute Pipeline
       — DESIGN: owns space definition and point selection
       — COMPUTE: owns exploration execution (parametric sweeps, optimization)
       — Mapping: ENT-D026.compute_pipeline_ref → COMPUTE Pipeline (TERM-C010)
       — Principle: P1
    c) Geometry ↔ Compute Dataset
       — DESIGN: owns geometry definition
       — COMPUTE: consumes as input data for simulation
       — Principle: P4
    d) FabricationMethod ↔ Compute Computation
       — DESIGN: owns manufacturing specification
       — COMPUTE: may run manufacturing simulation (CNC path, mold flow, etc.)
       — Principle: P1
    e) DesignEnvelope ↔ Compute Budget
       — DESIGN: requests compute resources within envelope
       — COMPUTE: enforces resource limits
       — Principle: P3
  Events emitted:   substrate.design.analysis.submitted,
                    substrate.design.space.exploration_requested
  Events consumed:  substrate.compute.execution.completed,
                    substrate.compute.pipeline.result_available,
                    substrate.compute.budget.exhausted
  Failure modes:    COMPUTE unavailable → new analyses queued. Existing results valid.
                    Release blocked if mandatory analyses incomplete.
  Retry policy:     Computation requests: max 3 retries, then queue for manual retry.

INT-D004: COMMUNICATION Integration — Depends on: DEP-D007 — Source: CROSS-SUBSTRATE-CONVENTIONS
  Protocol:        Cross-substrate event bus + reference resolution
  Auth:            Mutual substrate identity
  Integration points:
    a) DesignReview ↔ Communication Discourse + Protocol
       — DESIGN: owns review record and outcome
       — COMMUNICATION: owns review discourse process (speech acts, turn-taking)
       — Mapping: ENT-D015.discourse_ref → COMMUNICATION Discourse (TERM-M001)
       — Principle: P2 (DESIGN triggers review, COMMUNICATION delivers process)
    b) ChangeOrder approval ↔ Communication Commitment + Consensus
       — DESIGN: owns change content and impact
       — COMMUNICATION: owns approval discourse with tracked Commitments
       — Mapping: ENT-D017.approval_discourse_ref → COMMUNICATION Discourse
       — Principle: P2
    c) Annotation ↔ Communication Speech Act
       — DESIGN: owns Annotation as internal commentary
       — COMMUNICATION: hosts promoted Annotations as Speech Acts in Discourse
       — Promotion pattern: Annotation requiring structured response → COMMUNICATION
       — Principle: P2 (DESIGN triggers, COMMUNICATION hosts)
    d) Interface negotiation ↔ Communication Discourse
       — DESIGN: owns Interface definition and compatibility constraints
       — COMMUNICATION: hosts negotiation between teams as structured Discourse
       — Principle: P2
  Events emitted:   substrate.design.review.initiated,
                    substrate.design.change_order.review_requested,
                    substrate.design.annotation.promoted
  Events consumed:  substrate.communication.discourse.resolved,
                    substrate.communication.consensus.reached,
                    substrate.communication.commitment.fulfilled
  Failure modes:    COMMUNICATION unavailable → reviews degrade to Annotations.
                    Change order approvals queue. Design operations continue.
  Retry policy:     Event emission: max 10 retries, exponential backoff, DLQ.

INT-D005: PHYSICAL Integration — Depends on: DEP-D008 — Source: CROSS-SUBSTRATE-CONVENTIONS
  Protocol:        Cross-substrate event bus + reference resolution
  Auth:            Mutual substrate identity
  Integration points:
    a) Component ↔ PhysicalAsset
       — DESIGN: owns specification (what it should be)
       — PHYSICAL: owns operational instance (what it is)
       — Mapping: ENT-D004.component_id → PHYSICAL PhysicalAsset (TERM-P017)
       — Link established when manufactured. Maintained for lifecycle.
       — Principle: P4 (DESIGN owns spec, PHYSICAL owns instance)
    b) FabricationMethod ↔ Physical Process
       — DESIGN: owns how to make it (specification)
       — PHYSICAL: owns how to run the process (execution)
       — Mapping: ENT-D020 → PHYSICAL Process (TERM-P019)
       — This IS the design-to-manufacturing handoff (NG-D005)
       — Principle: P4
    c) Specification ↔ Physical SafetyEnvelope
       — DESIGN: owns safety requirements in Specification
       — PHYSICAL: owns runtime safety enforcement (SafetyEnvelope TERM-P014)
       — DESIGN safety Requirements inform PHYSICAL SafetyEnvelope configuration
       — Principle: P3 (DESIGN defines, PHYSICAL enforces)
    d) Tolerance ↔ Physical Measurement + Calibration
       — DESIGN: owns dimensional specification (what it should be)
       — PHYSICAL: owns measurement (what it actually is)
       — Feedback loop: DESIGN tolerance → PHYSICAL measures → comparison
       — Mapping: ENT-D011 values verified by PHYSICAL Measurement (TERM-P002)
       — Principle: P1 (DESIGN = specification, PHYSICAL = measurement)
    e) AnalysisResult ↔ Physical DigitalTwin
       — DESIGN: owns design-time analysis predictions
       — PHYSICAL: owns runtime simulation via DigitalTwin (TERM-P023)
       — Comparison validates design assumptions against operational reality
       — Principle: P1
  Events emitted:   substrate.design.component.released (triggers manufacturing),
                    substrate.design.specification.safety_requirements_updated,
                    substrate.design.fabrication_method.defined
  Events consumed:  substrate.physical.asset.commissioned,
                    substrate.physical.measurement.tolerance_deviation,
                    substrate.physical.calibration.completed,
                    substrate.physical.process_execution.completed
  Failure modes:    PHYSICAL unavailable → manufacturing handoff blocked. Design
                    operations continue. As-built feedback unavailable.
  Retry policy:     Event emission: max 10 retries, exponential backoff, DLQ.
  Mirror:           INT-P006 in SUBSTRATE-PHYSICAL.

INT-D006: Content Store Integration — Depends on: DEP-D003 — Source: DEP-D003
  Protocol:        Content Store API (binary artifact storage)
  Auth:            System credentials + per-artifact access control
  Integration points:
    — Geometry data (ENT-D006.content_ref)
    — Full analysis result files (ENT-D014.content_ref)
    — Drawing files (ENT-D022.content_ref)
    — Review minutes (ENT-D015.minutes_ref)
    — CAD native files, simulation meshes, rendered images
    — Import/export data packages
  Failure modes:    Content Store unavailable → metadata accessible. Binary content
                    temporarily unreadable. Design review impaired. No data loss.
  Retry policy:     Upload: retry with exponential backoff. Download: cache locally.

INT-D007: GOVERNANCE Integration — Depends on: DEP-D010 — Source: CROSS-SUBSTRATE-CONVENTIONS
  Protocol:        Cross-substrate event bus + reference resolution
  Auth:            Mutual substrate identity
  Purpose:         Comply with regulatory submission requirements and track standard lifecycle.
  Integration points:
    a) Regulatory submission ↔ Authority + ComplianceAssessment
       — GOVERNANCE: owns regulatory submission requirements and assessment
       — DESIGN: provides design artifacts for submission
       — Resolves OQ-D007
       — Principle: P3 (GOVERNANCE defines submission requirements)
    b) Standard ↔ NormLifecycle + RegulatoryChange
       — GOVERNANCE: tracks standard version changes as RegulatoryChanges (TERM-G025)
       — DESIGN: references standards as constraints (TERM-D012)
       — Principle: P4 (DESIGN owns standard reference, GOVERNANCE owns lifecycle tracking)
    c) DesignReview ↔ governance authority model
       — GOVERNANCE: Norms may define review requirements (who can approve, what requires review)
       — DESIGN: conducts reviews per those requirements
       — Principle: P3
    d) ChangeOrder ↔ re-submission determination
       — GOVERNANCE: Norms determine when design changes trigger regulatory re-submission
       — DESIGN: queries GOVERNANCE when ChangeOrder affects regulated designs
       — Principle: P3
  Events emitted:   substrate.design.component.released,
                    substrate.design.change_order.completed,
                    substrate.design.review.completed,
                    substrate.design.specification.safety_requirements_updated
  Events consumed:  substrate.governance.norm.effective,
                    substrate.governance.regulatory_change.adapted
  Failure modes:    GOVERNANCE unavailable → regulatory submission blocked. Design
                    operations continue. Standard lifecycle tracking deferred.
  Retry policy:     Event emission: max 10 retries, exponential backoff, DLQ.
  Mirror:           INT-G006 in SUBSTRATE-GOVERNANCE.

INT-D008: TEMPORAL Integration — Depends on: DEP-D011 — Source: CROSS-SUBSTRATE-CONVENTIONS
  Protocol:        Cross-substrate event bus + reference resolution
  Auth:            Mutual substrate identity
  Purpose:         Schedule design reviews and generate production schedules from BOMs.
  Integration points:
    a) DesignReview → Temporal Activity
       — DESIGN: owns review definition, participants, maturity gate
       — TEMPORAL: schedules as Activity (meeting type), creates Booking
       — Mapping: ENT-D015 → TEMPORAL Activity
       — Principle: P4 (DESIGN owns what to review, TEMPORAL owns when)
    b) BOM + FabricationMethod → production Schedule
       — DESIGN: owns BillOfMaterials (TERM-D021) and FabricationMethod (TERM-D020)
       — TEMPORAL: converts to Activities + Dependencies + ResourceRequirements
       — TEMPORAL solver produces production Schedule. See FLOW-T006.
       — Principle: P4 (DESIGN owns what to build, TEMPORAL owns when to build it)
  Events emitted:   substrate.design.review.scheduling_requested,
                    substrate.design.bom.updated,
                    substrate.design.fabrication_method.updated
  Events consumed:  substrate.temporal.booking.confirmed,
                    substrate.temporal.schedule.created
  Failure modes:    TEMPORAL unavailable → review scheduling degrades to manual.
                    Production schedule generation blocked. Design operations continue.
  Retry policy:     Event emission: max 10 retries, exponential backoff, DLQ.
  Mirror:           INT-T007 in SUBSTRATE-TEMPORAL.

INT-D009: SPATIAL Integration — Depends on: DEP-D012 — Source: CROSS-SUBSTRATE-CONVENTIONS
  Protocol:        Cross-substrate reference resolution (query-based, not event-driven)
  Auth:            Mutual substrate identity
  Purpose:         Obtain site context for design placement.
  Integration points:
    a) Site context query
       — DESIGN: requests SpatialFeatures within site vicinity, applicable
         SpatialConstraints (setbacks, flood zones, utility corridors), and
         terrain data (Raster DEM) from SPATIAL
       — SPATIAL: returns geographic context for site planning
       — Principle: P4 (DESIGN owns artifact, SPATIAL owns geographic context)
    b) Geometry ↔ SpatialGeometry coordinate mapping
       — DESIGN: Geometry (TERM-D006) in local coordinate system
       — SPATIAL: SpatialGeometry (TERM-S004) in Earth-referenced coordinate system
       — Linked via shared entity_id. Coordinate system enums have zero overlap.
       — For BIM: DESIGN owns IFC building model geometry; SPATIAL owns cadastral
         map footprint. Both co-exist for same real-world entity.
       — Principle: P4
  Events emitted:   (none — query-based integration)
  Events consumed:  (none — synchronous reference resolution)
  Failure modes:    SPATIAL unavailable → site context queries fail. Design operations
                    continue without geographic context. BIM placement blocked.
  Retry policy:     Reference resolution: max 3 retries, then degrade gracefully.
  Mirror:           INT-S004 in SUBSTRATE-SPATIAL.
```

### Cross-Substrate Event Topics

```
All events emitted or consumed by DESIGN across integration contracts INT-D001–D009.

Events Emitted by DESIGN:
  substrate.design.component.released               — Component version released for manufacturing
  substrate.design.change_order.completed            — Design modification approved and applied
  substrate.design.bom.derived                       — BOM generated from assembly
  substrate.design.bom.updated                       — BOM content changed
  substrate.design.review.completed                  — DesignReview maturity gate passed
  substrate.design.review.scheduling_requested       — DesignReview needs TEMPORAL scheduling
  substrate.design.analysis.completed                — AnalysisResult recorded
  substrate.design.configuration.validated           — Configuration validity confirmed
  substrate.design.material.property_discrepancy     — Material property mismatch detected
  substrate.design.specification.safety_requirements_updated — Safety spec changed
  substrate.design.fabrication_method.defined         — Manufacturing method specified
  substrate.design.fabrication_method.updated         — Manufacturing method changed

Events Consumed by DESIGN:
  substrate.business.organization.created             — Org provisioning (INT-D001)
  substrate.business.organization.suspended           — Org suspension (INT-D001)
  substrate.business.workflow.completed               — Business workflow done (INT-D001)
  substrate.business.entity.cost_updated              — Cost change (INT-D001)
  substrate.knowledge.proposition.confidence_changed  — Epistemic update (INT-D002)
  substrate.knowledge.source.reliability_changed      — Source trust change (INT-D002)
  substrate.compute.execution.completed               — Simulation result ready (INT-D003)
  substrate.communication.discourse.resolved          — Review discourse closed (INT-D004)
  substrate.communication.consensus.reached           — Design consensus (INT-D004)
  substrate.communication.commitment.fulfilled        — Commitment completed (INT-D004)
  substrate.physical.asset.commissioned               — PhysicalAsset from spec (INT-D005)
  substrate.physical.measurement.tolerance_deviation  — Out-of-tolerance measurement (INT-D005)
  substrate.physical.calibration.completed            — Instrument calibrated (INT-D005)
  substrate.physical.process_execution.completed      — Manufacturing step done (INT-D005)
  substrate.governance.norm.effective                  — Regulation active (INT-D007)
  substrate.governance.regulatory_change.adapted       — Standard version changed (INT-D007)
  substrate.temporal.booking.confirmed                 — Review time slot confirmed (INT-D008)
  substrate.temporal.schedule.created                  — Production schedule ready (INT-D008)
```

---

## 9. AUTHORIZATION & ACCESS MODEL

### Resources

```
RES-D001: Requirement — maps to: ENT-D001
RES-D002: Specification — maps to: ENT-D002
RES-D003: DesignRationale — maps to: ENT-D003
RES-D004: Component — maps to: ENT-D004
RES-D005: Assembly — maps to: ENT-D005
RES-D006: Geometry — maps to: ENT-D006
RES-D007: Topology — maps to: ENT-D007
RES-D008: Material — maps to: ENT-D008
RES-D009: MaterialProperty — maps to: ENT-D009
RES-D010: Constraint — maps to: ENT-D010
RES-D011: Tolerance — maps to: ENT-D011
RES-D012: Standard — maps to: ENT-D012
RES-D013: TestCriterion — maps to: ENT-D013
RES-D014: AnalysisResult — maps to: ENT-D014
RES-D015: DesignReview — maps to: ENT-D015
RES-D016: DesignVersion — maps to: ENT-D016
RES-D017: ChangeOrder — maps to: ENT-D017
RES-D018: Configuration — maps to: ENT-D018
RES-D019: Variant — maps to: ENT-D019
RES-D020: FabricationMethod — maps to: ENT-D020
RES-D021: BillOfMaterials — maps to: ENT-D021
RES-D022: Drawing — maps to: ENT-D022
RES-D023: Interface — maps to: ENT-D023
RES-D024: DesignEnvelope — maps to: ENT-D024
RES-D025: ParametricRelation — maps to: ENT-D025
RES-D026: DesignSpace — maps to: ENT-D026
RES-D027: Event — maps to: ENT-D027
RES-D028: Annotation — maps to: ENT-D028
```

### Permission Matrix

```
| Actor \ Resource       | Component | Assembly | Geometry | Material | Constraint | Tolerance | Analysis | Review   | ChangeOrder | Config   | BOM      | Drawing  |
|------------------------|-----------|----------|----------|----------|------------|-----------|----------|----------|-------------|----------|----------|----------|
| ACT-D001 (Designer)    | CRUD      | CRUD     | CRUD     | read,assign | CRUD    | CRUD      | create,read | schedule | create,read | CRUD   | read,override | CRUD |
| ACT-D002 (Engineer)    | read,modify | read,modify | read | read     | CRUD      | CRUD      | CRUD     | schedule,review | create,read | read | read  | read     |
| ACT-D003 (Authority)   | approve   | approve  | read     | approve  | approve,waive | read   | accept   | decide   | approve     | baseline | approve  | approve  |
| ACT-D004 (Narrow AI)   | CRUD*     | read*    | CRU*     | read*    | eval*     | read*     | create*  | read*    | read*       | read*    | derive*  | read*    |
| ACT-D005 (General AI)  | CRUD*     | CRUD*    | CRUD*    | read,assign* | CRUD* | CRU*      | CRUD*    | read*    | create*     | read*    | derive*  | read*    |
| ACT-D006 (External)    | read†     | read†    | read†    | read†    | read†     | read†     | read†    | read†    | read†       | read†    | read†    | read†    |
| ACT-D007 (Auditor)     | read      | read     | read     | read     | read      | read      | read     | read     | read        | read     | read     | read     |
| ACT-D008 (Mfg System)  | read‡     | read‡    | read‡    | read‡    | read‡     | read‡     | read‡    | read‡    | read‡       | read‡    | read‡    | read‡    |

* = Within DesignEnvelope only. Effective permission = stated ∩ DesignEnvelope ∩ Epistemic Envelope.
    AI agents MUST NOT: approve releases, approve ChangeOrders, decide DesignReview outcomes
    for safety-critical or regulatory artifacts (ACT-D003 authority non-delegable for these).
† = Validated, rate-limited, sandboxed per TRUST-D001.
‡ = Released artifacts only. Cannot access in-progress designs.
```

### Ownership Rules

```
**Ownership rules:**
- Events are owned by the System. No Actor may modify or delete Events. Append-only.
- DesignVersions are owned by the System. Immutable once created.
- DesignRationale is immutable once created. New rationales supersede, not modify.
- Release approval (Component/Assembly/Specification) requires ACT-D003 (Design Authority).
  This MUST NOT be delegated to AI agents for safety-critical or regulatory artifacts.
- ChangeOrder approval requires ACT-D003. Emergency changes require post-facto review.
- DesignEnvelopes are granted by ACT-D003 and enforced by the system. Auto-expire.
- Standards (ENT-D012) are immutable once referenced by a released design.
- Configuration validity is system-computed, not actor-declared.

**Delegation rules:**
- ACT-D001 (Designer) may delegate to ACT-D004/D005 (AI) within DesignEnvelope scope.
  Delegation is logged and bounded by envelope validity period.
- ACT-D003 (Design Authority) authority is NON-DELEGABLE to AI for: release approval of
  safety-critical artifacts, regulatory submissions, safety requirement approval.
- ACT-D008 (Manufacturing System) operates in read-only mode on released artifacts only.
  Manufacturing deviations reported back via event bus — DESIGN evaluates disposition.

**IP-aware access control:**
- Supply chain (TRUST-D004 network boundary): supplier sees only their assigned Component
  scope. OEM sees supplier's interface compliance but not internal design details.
- IP classification per entity: public | internal | confidential | restricted.
  Access filtered by IP classification level of authenticated principal.

**Unauthenticated access:**
- NONE. All access requires authentication via DEP-D002.

**Session model:**
- Sessions bound to authenticated identity (DEP-D002).
- AI agent sessions bound to DesignEnvelope validity period.
- Long-lived design sessions support disconnected operation (local workstation cache)
  with sync-on-reconnect.
```

---

## 10. SECURITY & PRIVACY MODEL

### Data Classification

```
CLASS-D001: IP-Restricted — Entities: Geometry (proprietary designs), FabricationMethod
            (trade secrets), DesignRationale (competitive intelligence), AnalysisResult
            (performance data). Highest protection. Unauthorized access = competitive harm.

CLASS-D002: IP-Confidential — Entities: Component specifications, Assembly structures,
            BOM details, Material selections, Tolerance specifications. High protection.
            Shared only within organization and with authorized supply chain partners.

CLASS-D003: Configuration — Entities: Standard references, DesignEnvelope configs,
            Configuration baselines. Moderate protection. Integrity important.

CLASS-D004: Audit — Entities: Events (all types), DesignVersions. Highest integrity.
            Append-only. Tamper-evident. Used for regulatory compliance.

CLASS-D005: PII — Entities: Actor references in Events, review participants,
            DesignRationale decided_by. Privacy-protected per applicable regulations.
```

### Threat Model

```
THREAT-D001: Design IP theft — attacker exfiltrates proprietary geometry/specifications
             — Mitigation: IP-classification-based access control. Encryption at rest
               and in transit. Supply chain access scoped to assigned Components only.
               Watermarking for exported geometry. Download audit logging.
             — Source: UNK-D005

THREAT-D002: Unauthorized design modification — attacker modifies released designs
             — Mitigation: Released designs immutable (DesignVersion). Changes only via
               ChangeOrder with Design Authority approval. Cryptographic hash on
               Geometry content. Event-sourced audit trail detects tampering.
             — Source: ASM-D008

THREAT-D003: Counterfeit component insertion — attacker substitutes inferior materials/parts
             — Mitigation: BOM traceability to approved suppliers. Material certification
               chain. As-built Configuration tracking. PHYSICAL Measurement verification
               against DESIGN Tolerance specifications.
             — Source: SRC-D014, SRC-D015

THREAT-D004: AI design manipulation — malicious actor manipulates AI agent's design outputs
             — Mitigation: DesignEnvelope bounds AI authority. All AI outputs require same
               TestCriteria and DesignReview as human outputs. No shortcuts. Convergence
               verification for AI-generated analysis. Anomaly detection on design patterns.
             — Source: ASM-D005

THREAT-D005: Event log tampering — attacker modifies design audit trail
             — Mitigation: Append-only event store. Cryptographic hash chain.
               Cross-substrate event projection. Regular integrity verification.
               Write-once media for regulated industries.
             — Source: ASM-D008

THREAT-D006: Standard reference manipulation — attacker substitutes incorrect standards
             — Mitigation: Standards immutable once referenced. Content hashes verified.
               Authoritative source linkage. Version pinning prevents silent substitution.
             — Source: SRC-D008
```

### Abuse Cases

```
ABUSE-D001: AI generates geometry that satisfies automated checks but fails in practice
  Given:  AI agent with design authority within DesignEnvelope
  When:   Agent generates geometry optimized to pass DRC/automated checks but
          with subtle defects (stress concentrators, thin walls, etc.)
  Then:   All AI designs pass SAME DesignReviews as human designs. Human engineer
          review required before release (requires_human_review: true for release_prepare).
          AnalysisResults must have convergence_confirmed. Physical testing via
          PHYSICAL validates actual behavior. Pattern detection flags statistical anomalies.

ABUSE-D002: Designer bypasses review by incrementally releasing small changes
  Given:  Designer with Component modify authority
  When:   Designer makes many small changes, each below review threshold, that
          collectively constitute a major design change
  Then:   Configuration revalidation triggered on ANY member change. Cumulative
          change tracking flags significant divergence from baseline. ChangeOrder
          required for released designs — no incremental bypass possible.

ABUSE-D003: Supply chain partner extracts design IP beyond authorized scope
  Given:  Supplier with read access to assigned Component scope
  When:   Supplier attempts to access adjacent Components, parent Assembly, or
          other supplier designs
  Then:   Access filtered by supply chain scope. IP-classification enforcement.
          All access logged. Anomalous query patterns flagged. Export watermarked.
```

---

## 11. BEHAVIORAL CONTRACTS

### Invariants (must ALWAYS hold)

```
INV-D001: Every released Specification has all Requirements with at least one
          TestCriterion where result_status ≠ untested.
          — Source: Failure Definition (a), CAP-D013

INV-D002: Every valid Configuration has all member Interfaces compatible and all
          member Constraints simultaneously satisfiable.
          — Source: Failure Definition (b), CAP-D019

INV-D003: Every approved ChangeOrder has impact_analysis identifying ALL affected
          Components, Assemblies, and Configurations.
          — Source: Failure Definition (c), CAP-D018

INV-D004: Every Tolerance stack-up that passes individual part checks MUST also
          pass assembly-level stack analysis.
          — Source: Failure Definition (d), CAP-D016, ASM-D011

INV-D005: The Event log is append-only. No Event may be modified or deleted.
          — Source: Failure Definition (e), CAP-D030, ASM-D008

INV-D006: DesignVersion entities are immutable. No modification after creation.
          — Source: TERM-D016, ASM-D006

INV-D007: DesignRationale entities are immutable. Superseded, not modified.
          — Source: TERM-D003, ASM-D002

INV-D008: DesignEnvelope authority MUST NOT exceed the intersection of Business
          Agent Envelope and Epistemic Envelope.
          — Source: TERM-D024, CROSS-SUBSTRATE-CONVENTIONS §1

INV-D009: Standards referenced by released designs are immutable. Supersession
          tracked but original references preserved.
          — Source: TERM-D012, TRUST-D005

INV-D010: Every Component in a released Assembly has a valid cross-reference to
          its parent Assembly. No orphan Components in released Assemblies.
          — Source: TERM-D004, TERM-D005

INV-D011: Every Constraint with verification_method: automated_rule_check has a
          machine-parseable expression.
          — Source: TERM-D010, CAP-D009

INV-D012: Assembly composition is acyclic. No Assembly contains itself at any
          depth of recursion.
          — Source: TERM-D005, CAP-D002
```

### Preconditions

```
PRE-D001: Before releasing a Component: geometry exists (for physical), material
          assigned (for physical), all Requirements tested, DesignReview approved,
          Configuration valid (if in Assembly), BOM complete (if Assembly).
          — Source: SM-D002, CAP-D026

PRE-D002: Before approving a ChangeOrder: impact_analysis complete, all affected
          entities identified, cost estimate provided (if applicable).
          — Source: SM-D003, CAP-D018

PRE-D003: Before establishing a Configuration baseline: all Variants resolved,
          all Interfaces compatible, all Constraints satisfied, validity_status = valid.
          — Source: SM-D005, CAP-D019

PRE-D004: Before AI Agent performs design operation: DesignEnvelope active (within
          valid_from/valid_until), operation within scope, target entity within scope.
          — Source: FLOW-D007, CAP-D029

PRE-D005: Before accepting AnalysisResult: convergence_confirmed = true (SHOULD),
          assumptions documented, limitations documented.
          — Source: ENT-D014, CAP-D014

PRE-D006: Before transitioning Specification to released: all Requirements have
          testable = true, all TestCriteria have result_status ≠ untested, all
          mandatory DesignReviews completed with outcome = approved.
          — Source: SM-D006, CAP-D013, CAP-D026
```

### Postconditions

```
POST-D001: After releasing a Component: immutable DesignVersion created, Event
           emitted, status = released, no further modification without ChangeOrder.
           — Source: SM-D002

POST-D002: After completing a ChangeOrder: all affected entities have new
           DesignVersions, affected Configurations revalidated, Event emitted.
           — Source: SM-D003, FLOW-D002

POST-D003: After Configuration validation: validity_status reflects actual state
           (valid/invalid), validation_errors populated if invalid.
           — Source: FLOW-D006

POST-D004: After DesignReview completion: outcome recorded, action_items tracked,
           entity status updated per outcome.
           — Source: SM-D004

POST-D005: After BOM derivation: all Components in Assembly tree represented,
           quantities correct, cost/mass estimates computed where data available.
           — Source: FLOW-D005

POST-D006: After import: all imported entities have provenance (import source,
           timestamp), topology validated, automated checks executed.
           — Source: FLOW-D008
```

### Forbidden States

```
FORBID-D001: A released Specification with any Requirement where testable = false.
             — Enforcement: SM-D006 guards, CAP-D013

FORBID-D002: A released Specification with any TestCriterion where result_status = untested.
             — Enforcement: SM-D006 guards, CAP-D013

FORBID-D003: A valid Configuration with incompatible member Interfaces.
             — Enforcement: FLOW-D006, CAP-D019

FORBID-D004: A valid Configuration with unsatisfiable member Constraints.
             — Enforcement: FLOW-D006

FORBID-D005: An approved ChangeOrder without impact_analysis.
             — Enforcement: SM-D003 guards, CAP-D018

FORBID-D006: An assembly-level tolerance stack pass when individual tolerances
             cause assembly failure.
             — Enforcement: CAP-D016, FLOW-D006

FORBID-D007: A modified or deleted Event.
             — Enforcement: CAP-D030, append-only store

FORBID-D008: A modified DesignVersion or DesignRationale.
             — Enforcement: INV-D006, INV-D007, system enforcement

FORBID-D009: An AI Agent operating outside its DesignEnvelope.
             — Enforcement: FLOW-D007, CAP-D029

FORBID-D010: Blind trust in simulation results: an AnalysisResult accepted without
             documented assumptions and limitations.
             — Enforcement: ENT-D014 constraints, PRE-D005

FORBID-D011: A Geometry content_hash mismatch (stored content differs from hash).
             — Enforcement: ENT-D006 constraints, integrity checks

FORBID-D012: A circular Assembly reference (Assembly containing itself).
             — Enforcement: INV-D012, CAP-D002
```

### Failure Guarantees

```
FAIL-D001: If COMPUTE is unavailable, design creation and modification continue.
           New analyses queue. Existing AnalysisResults remain valid. Release blocked
           only if mandatory analyses incomplete.
           — Source: DEP-D006

FAIL-D002: If COMMUNICATION is unavailable, design reviews degrade to Annotations.
           Change order approvals queue. Design operations continue.
           — Source: DEP-D007

FAIL-D003: If KNOWLEDGE is unavailable, cached material data used. Designs flagged
           with stale-data warning. Material confidence updates deferred.
           — Source: DEP-D005

FAIL-D004: If PHYSICAL is unavailable, manufacturing handoff blocked. Design
           operations continue. As-built feedback deferred.
           — Source: DEP-D008

FAIL-D005: If Content Store is unavailable, metadata accessible. Binary geometry/
           drawings temporarily unreadable. No data loss (parametric definitions inline).
           — Source: DEP-D003

FAIL-D006: If constraint solver fails on complex assembly, partial results returned
           with unsolved constraints flagged. Design operations continue for entities
           not depending on unsolved constraints.
           — Source: UNK-D002

FAIL-D007: If import validation fails, partial import with flagged entities. Valid
           entities imported; invalid entities rejected with specific error descriptions.
           No silent data corruption.
           — Source: FLOW-D008

FAIL-D008: If DesignEnvelope check fails, operation rejected with specific violation
           description. Audit log entry created. No partial design modification.
           — Source: FLOW-D007
```

---

## 12. DECISION POINTS (WHERE THE SYSTEM CHOOSES)

> Decision points identify where runtime logic must choose between options.
> Each decision has explicit selection rules and fallbacks. No decision is
> left to "implementation discretion."

```
DEC-D001: Constraint Satisfaction Strategy
          — Context: CAP-D010, FLOW-D006 — Source: Property D6 (Constraint Primacy)
  Inputs:          Set of Constraints on a Component/Assembly, current parameter values
  Options:         Satisfied | Violated (with specific violators) | Underdetermined
  Selection rule:
    1. Evaluate all automated_rule_check Constraints first (fast, deterministic)
    2. For each constraint with status: active and severity: mandatory:
       a) Parse expression
       b) Substitute current parameter values
       c) Evaluate: true → satisfied, false → violated, unknown → underdetermined
    3. If any mandatory constraint violated: report all violations (not just first)
    4. If any underdetermined: report as needing analysis or more data
    5. Preferred constraints (severity: preferred): report as warnings, not blockers
  Fallback:        If constraint solver times out on complex assembly, return partial
                   results with unsolved constraints flagged (FAIL-D006).

DEC-D002: Design Space Exploration Strategy Selection
          — Context: FLOW-D007a, CAP-D027 — Source: Property D2 (Combinatorial Explosion)
  Inputs:          DesignSpace definition (parameters, constraints, objectives, budget)
  Options:         exhaustive | random | latin_hypercube | bayesian | genetic |
                   topology_optimization | gradient | manual
  Selection rule:
    IF parameter_count ≤ 3 AND total_combinations ≤ 10,000: exhaustive
    ELSE IF parameter_count ≤ 10 AND objectives.length = 1: gradient (if differentiable)
    ELSE IF parameter_count ≤ 50 AND objectives.length ≥ 2: genetic (NSGA-II)
    ELSE IF compute_budget limited: bayesian (sample-efficient)
    ELSE IF structural topology unknown: topology_optimization (SIMP/BESO)
    ELSE: latin_hypercube (space-filling, no assumptions)
  Note:            User may override. This is the RECOMMENDED default, not enforced.

DEC-D003: Change Impact Cascade
          — Context: FLOW-D002, CAP-D018 — Source: Failure Definition (c)
  Inputs:          ChangeOrder with affected_entities[], Assembly hierarchy, Configuration data
  Options:         Impact set = all entities transitively affected
  Selection rule:
    1. Start with directly affected entities
    2. For each affected Component: find parent Assemblies (upward)
    3. For each affected Assembly: find Configurations containing it
    4. For each affected Interface: find both sides and their parents
    5. For each affected Material: find all Components using it
    6. For each affected Standard: find all Constraints referencing it
    7. For each affected Tolerance: find assembly stack-ups referencing it
    8. Union all discovered entities = impact set
    9. Warn if impact set exceeds 100 entities (major change)
  Fallback:        If hierarchy traversal exceeds depth limit (1000), report as
                   "potentially unbounded impact" — human review required.

DEC-D004: BOM Type Transformation (eBOM → mBOM)
          — Context: FLOW-D005, CAP-D024 — Source: SRC-D004
  Inputs:          Engineering BOM (as-designed), manufacturing process requirements
  Options:         Direct mapping (eBOM = mBOM) | Transformation required
  Selection rule:
    IF all Components have FabricationMethod with process_type matching eBOM structure:
       mBOM = eBOM (direct mapping)
    ELSE:
       Transform: reorder by manufacturing sequence, consolidate raw materials,
       add process-specific items (fixtures, consumables), split assemblies by
       manufacturing station. Each override from eBOM tracked in BOM.overrides.

DEC-D005: AnalysisResult Acceptance
          — Context: FLOW-D003, CAP-D014 — Source: FORBID-D010
  Inputs:          AnalysisResult with convergence_confirmed, assumptions, limitations
  Options:         Accept | Reject | Request additional analysis
  Selection rule:
    MUST reject if: assumptions not documented (PRE-D005)
    SHOULD reject if: convergence_confirmed = false AND analysis_type is structural,
                      thermal, or fatigue (safety-relevant)
    SHOULD request additional if: limitations indicate boundary effects or mesh sensitivity
    Acceptable if: convergence confirmed, assumptions documented, limitations acceptable
                   for the design's criticality level
  Note:            Final decision by ACT-D002 (Engineer). System provides recommendation.

DEC-D006: Geometry Representation Selection
          — Context: CAP-D003, TERM-D006 — Source: Property D4 (Scale Spanning)
  Inputs:          Component domain, scale, intended use
  Options:         representation_type enum values
  Selection rule:
    molecular domain (angstrom-nm): molecular_graph or quantum_structure
    IC layout (nm-mm): layout_2d
    PCB/mechanical (um-m): brep (modeling), mesh (analysis), 2d_profile (sections)
    architectural (m-km): brep (components), parametric (families)
    schematic (logical): schematic
    manufacturing (any): mesh (simulation), 2d_profile (toolpath), voxel (additive)
    surveying/scanning: point_cloud
  Note:            Multiple representations for same Component allowed (Drawing ≠ Geometry).
```

---

## 13. CONCURRENCY & ORDERING

```
CONC-D001: Concurrent Design Modification
  Problem:         Multiple designers modifying the same Component/Assembly simultaneously.
  Strategy:        Optimistic concurrency with version-based conflict detection.
  Rules:
    - Each modification targets a specific entity version.
    - If entity version has changed since read, modification is rejected with conflict.
    - Conflicting designer must re-read, merge manually, and resubmit.
    - No automatic merge for design data (unlike text — geometry merges are
      semantically complex and potentially dangerous).
    - Released entities cannot be modified without ChangeOrder (no conflict possible).
  Implementation:  Version field on all entities. Compare-and-swap on write.

CONC-D002: Concurrent Analysis Submission
  Problem:         Multiple analyses running on different versions of the same entity.
  Strategy:        Allow concurrent analyses. Each AnalysisResult linked to specific
                   entity_version. Results from older versions flagged as potentially stale.
  Rules:
    - Analyses are non-mutating (they read design data, don't modify it).
    - Multiple concurrent analyses on same entity allowed.
    - When entity version increments, existing in-progress analyses continue but
      their results are tagged with analyzed_version ≠ current_version warning.

CONC-D003: Configuration Validation Ordering
  Problem:         Configuration validity changes when any member changes.
  Strategy:        Revalidation triggered on any member change. Results are eventually
                   consistent (validation may take time for complex configurations).
  Rules:
    - Member change → queue configuration revalidation.
    - Validation is idempotent (rerunning produces same result for same state).
    - If member changes again during validation, re-queue (latest state wins).
    - Configuration consumers check validity_status before use.

CONC-D004: ChangeOrder Conflict
  Problem:         Two ChangeOrders affecting the same entities simultaneously.
  Strategy:        Detect conflict at submission. Require human resolution.
  Rules:
    - When ChangeOrder submitted, check for other active ChangeOrders affecting
      overlapping entities.
    - If overlap detected, flag conflict. Both ChangeOrders visible to reviewers.
    - Design Authority decides: merge, prioritize, or serialize.
    - Emergency ChangeOrders may proceed in parallel if non-overlapping scope.

CONC-D005: Event Ordering
  Problem:         Ensure audit trail reflects actual sequence of operations.
  Strategy:        Per-entity event ordering (same as all peer substrates per
                   CROSS-SUBSTRATE-CONVENTIONS §3).
  Rules:
    - Events for the same entity are delivered in order.
    - No cross-entity ordering guarantee.
    - Consumers must be idempotent (at-least-once delivery).
    - trace_id and caused_by enable causal reconstruction across entities.
```

---

## 14. ERROR HANDLING & RECOVERY

### Error Taxonomy

```
ERR-D001: Validation Error — input data fails schema validation
          Recovery: reject with specific field-level errors. No state change.

ERR-D002: Authorization Error — actor lacks permission for operation
          Recovery: reject. Audit log. No state change. Suggest correct actor.

ERR-D003: Entity Not Found — referenced entity does not exist
          Recovery: reject. No state change.

ERR-D004: DesignEnvelope Violation — AI agent operation outside envelope
          Recovery: reject. Audit log with violation details. Event emitted.
          No partial modification. Suggest envelope renewal if expired.

ERR-D005: Geometry Invalid — imported or generated geometry topologically invalid
          Recovery: reject geometry update. Report specific issues (self-intersections,
          non-manifold edges, open shells for solid models). Existing geometry preserved.

ERR-D006: Prerequisites Not Met — operation attempted before required preconditions
          Recovery: reject with checklist of unmet prerequisites. No state change.

ERR-D007: Circular Reference — Assembly composition would create cycle
          Recovery: reject addition. Report cycle path. No state change.

ERR-D008: Interface Incompatible — connected Components have incompatible interfaces
          Recovery: report specific incompatibility. Interface status → broken.
          Configuration revalidation triggered.

ERR-D009: Tolerance Stack Failure — individual tolerances valid but assembly fails
          Recovery: report stack analysis results with critical contributors.
          Flag affected Configuration as invalid. Suggest remediation.

ERR-D010: Constraint Expression Parse Error — automated check expression unparseable
          Recovery: reject constraint definition. Report parse error location.

ERR-D011: Compute Unavailable — COMPUTE dependency down for analysis submission
          Recovery: queue analysis request. Design operations continue. Release
          blocked if mandatory analysis incomplete. Retry with backoff.

ERR-D012: Impact Analysis Incomplete — ChangeOrder submitted without full impact
          Recovery: reject submission. Report missing impact areas. No state change.

ERR-D013: Configuration Invalid — baseline attempted on invalid configuration
          Recovery: reject baseline. Report validation_errors. Suggest resolution.

ERR-D014: DFM Incompatibility — design geometry incompatible with fabrication process
          Recovery: warn (not block). Report specific incompatibility. Designer decides.

ERR-D015: Compute Budget Exceeded — design space exploration exceeds allocated resources
          Recovery: stop exploration. Return partial results. Report points explored.

ERR-D016: Import Format Unsupported — external format not recognized
          Recovery: reject import. Report supported formats.

ERR-D017: Import Validation Failed — imported data fails DESIGN validation
          Recovery: partial import if possible (valid entities imported, invalid rejected).
          Report per-entity validation results. No silent data corruption.

ERR-D018: Geometry Topology Invalid — imported geometry has topological errors
          Recovery: report specific topology issues. Partial import with flagged entities.

ERR-D019: Version Conflict — concurrent modification detected
          Recovery: reject update. Return current version. Designer must re-read and merge.

ERR-D020: Material Confidence Below Threshold — material data confidence too low for use
          Recovery: warn for general designs. Block for safety-critical designs
          (confidence < 0.5 per TRUST-D003). Suggest higher-confidence source.
```

---

## 15. PERSISTENCE REQUIREMENTS

```
PERS-D001: Event Store
  Data:      All Events (ENT-D027)
  Model:     Append-only, immutable, event-sourced
  Retention: General designs: minimum 30 years
             Regulated products (medical, aerospace, automotive): minimum lifetime
               of product + 10 years (per FDA/FAA/IATF requirements)
             Buildings and infrastructure: minimum 100 years (ASM-D012)
             Nuclear facilities: per NRC requirements (potentially millennia)
  Format:    Non-proprietary. Must be readable without vendor tools. Open schema.
  Integrity: Cryptographic hash chain. Tamper-evident. Regular verification.

PERS-D002: Design Entity Store
  Data:      All entities (ENT-D001 through ENT-D028 metadata)
  Model:     Event-sourced with materialized views. Any entity state reconstructable
             from event history.
  Retention: Same as Event Store (entities derived from events)
  Format:    Non-proprietary (ASM-D010, ASM-D012)

PERS-D003: Content Store (binary artifacts)
  Data:      Geometry data, drawing files, analysis result files, CAD native files,
             simulation meshes, import/export packages
  Model:     Content-addressable (SHA-256 hash). Immutable once stored.
  Retention: Same as associated entities
  Format:    Long-term formats: STEP AP242, IFC 4.3, IPC-2581, PDF/A for drawings.
             CAD native formats accepted but MUST be accompanied by open format copy
             for long-term accessibility (ASM-D012).
  Integrity: Content hash verified on read. Corruption detection and repair from
             redundant copies.

PERS-D004: Offline/Disconnected Operation
  Data:      Working set of design entities for local workstation operation
  Model:     Cached copy with sync-on-reconnect. Conflict detection on sync.
  Retention: Session-scoped. Cleared on sync completion.
  Constraint: Offline modifications are provisional. Released designs cannot be
              modified offline (requires ChangeOrder which requires connectivity).
```

---

## 16. MIGRATION & ONBOARDING

> SUBSTRATE-DESIGN is a new specification. There is no "migration from SUBSTRATE-DESIGN
> v0.x." However, onboarding from legacy design systems is critical.

### Onboarding Paths

```
ONBOARD-D001: From CAD/CAM Systems (SolidWorks, CATIA, NX, Creo, Fusion 360)
  Import format:   STEP AP242 (preferred), STEP AP203/AP214, IGES (legacy)
  Entities mapped: Component, Assembly, Geometry (brep/mesh), Material (basic),
                   Tolerance (from model annotations), Drawing (from drawing sheets)
  Not imported:    Parametric history (representation-dependent), feature tree
                   (tool-specific), sketches (tool-specific)
  Validation:      Geometry topology check. Material property completeness check.
                   Tolerance completeness check.

ONBOARD-D002: From EDA Systems (Altium, KiCad, Cadence, Synopsys)
  Import format:   IPC-2581 (preferred), ODB++, EDIF, GDSII/OASIS (IC layout)
  Entities mapped: Component (parts), Assembly (board), Geometry (layout_2d/schematic),
                   BillOfMaterials (from schematic), Interface (nets),
                   Constraint (design rules), Topology (netlist)
  Not imported:    Simulation models (SPICE → COMPUTE), library management (tool-specific)
  Validation:      DRC/ERC execution on imported data. Net connectivity verification.

ONBOARD-D003: From BIM Systems (Revit, ArchiCAD, Tekla)
  Import format:   IFC 4.3 (preferred), IFC 2x3 (legacy), COBie (data exchange)
  Entities mapped: Component (building elements), Assembly (building model),
                   Geometry (brep), Material (from element properties), Standard
                   (from classification systems), Interface (spatial relationships)
  Not imported:    Parametric families (tool-specific), schedules (→ BUSINESS)
  Validation:      Clash detection. Classification completeness check.

ONBOARD-D004: From PLM Systems (Windchill, Teamcenter, ENOVIA)
  Import format:   OSLC (preferred), PLM XML, custom API integration
  Entities mapped: Component (parts), Assembly (product structure), BillOfMaterials,
                   ChangeOrder (change history), Configuration (baselines),
                   DesignVersion (revision history), Standard (referenced standards)
  Not imported:    Workflow definitions (→ BUSINESS), user management (→ Identity Provider)
  Validation:      BOM structure integrity. Configuration consistency check.
                   ChangeOrder history completeness.

ONBOARD-D005: From Requirements Tools (DOORS, Jama, Polarion)
  Import format:   ReqIF (preferred), CSV with mapping template
  Entities mapped: Requirement (with hierarchy), TestCriterion (V&V items),
                   Specification (modules/documents), Traceability (links)
  Not imported:    Workflow state (tool-specific), change history (tool-specific)
  Validation:      Requirement testability check. Traceability completeness check.

ONBOARD-D006: From Molecular Design (Schrödinger, ChemDraw, RDKit)
  Import format:   SDF/MOL (structures), SMILES/InChI (identifiers), PDB/CIF (crystals)
  Entities mapped: Component (molecules), Geometry (molecular_graph), Material
                   (compounds), MaterialProperty (calculated/measured properties),
                   Constraint (synthetic accessibility, stability)
  Not imported:    Force field parameters (→ COMPUTE), docking results (→ AnalysisResult)
  Validation:      Molecular structure validity. Property completeness check.
```

---

## 17. OPERATIONAL PROFILE

```
OPS-D001: Throughput Targets (per Organization deployment)
  Design operations:
    Small org (1-50 designers):     100-1,000 operations/day
    Medium org (50-500 designers):  1,000-50,000 operations/day
    Large org (500+ designers):     50,000-500,000 operations/day
  Analysis submissions:             10-100 per designer per day (burst during review cycles)
  Import/export:                    1-100 per day (batch operations)
  Event emission:                   1:1 with operations (every operation produces an event)

OPS-D002: Latency Targets
  Interactive modeling (geometry update):     < 500ms on local workstation
  Constraint evaluation (single entity):      < 1s
  Constraint evaluation (full assembly):      < 30s for ≤1,000 components
  DRC/automated rule check:                  < 5min for ≤10,000 rules
  BOM derivation:                            < 10s for ≤10,000 components
  Configuration validation:                  < 30s for ≤1,000 members
  Tolerance stack-up (Monte Carlo, 10K iterations): < 60s
  Import (STEP AP242, typical assembly):     < 5min
  Event persistence:                         < 100ms
  Cross-substrate event delivery:            < 5s (per CROSS-SUBSTRATE-CONVENTIONS)

OPS-D003: Storage Estimates
  Per Component (metadata):                  5-50 KB
  Per Geometry (binary, Content Store):      100 KB - 100 MB (varies by representation)
  Per AnalysisResult (binary, Content Store): 1 MB - 10 GB (varies by analysis type)
  Per Drawing (Content Store):               500 KB - 50 MB
  Per Event:                                 1-5 KB
  Typical org annual growth:                 1-100 TB (dominated by Geometry and Analysis)
  Long-term retention (100 years):           Design data MUST remain accessible.
                                             Format migration MUST be supported.
```

---

## 18. TEST PLAN

> Every test is traceable to capabilities (CAP-D), state machines (SM-D),
> data flows (FLOW-D), or invariants (INV-D). Tests are organized by
> capability cluster.

### Modeling Tests

```
TEST-D001: Create Component with all required attributes.
           Verify: entity persisted, status: concept, Event emitted.
           Traces to: CAP-D001, ENT-D004

TEST-D002: Create Assembly with Components. Verify recursive composition works.
           Attempt circular reference. Verify rejection (ERR-D007).
           Traces to: CAP-D002, INV-D012

TEST-D003: Store Geometry with each representation_type (brep, mesh, parametric,
           layout_2d, schematic, molecular_graph). Verify content_hash integrity.
           Traces to: CAP-D003, ENT-D006

TEST-D004: Define Topology independently of Geometry. Modify Geometry without
           changing Topology. Verify Topology preserved. Modify Topology.
           Verify Geometry flagged for review.
           Traces to: CAP-D004, ENT-D007

TEST-D005: Assign Material to Component. Substitute Material. Verify
           DesignRationale created for substitution.
           Traces to: CAP-D005, ENT-D008, ENT-D003

TEST-D006: Define ParametricRelation between two Components. Change one
           parameter. Verify dependent parameter updated. Verify violated
           relation flagged immediately.
           Traces to: CAP-D006, ENT-D025

TEST-D007: Define Interface between two Components. Modify one side.
           Verify compatibility revalidation triggered.
           Traces to: CAP-D007, ENT-D023

TEST-D008: Create spatially-anchored Annotation on Geometry. Create action_item
           Annotation. Verify resolution tracking.
           Traces to: CAP-D008, ENT-D028
```

### Constraint & Verification Tests

```
TEST-D009: Define Constraint with verification_method: automated_rule_check.
           Verify machine evaluation without human intervention.
           Traces to: CAP-D009, ENT-D010

TEST-D010: Add Constraint to child Component that affects parent Assembly.
           Verify bidirectional propagation surfaces constraint at Assembly level.
           Traces to: CAP-D010, Property D6

TEST-D011: Define GD&T Tolerance per ASME Y14.5 (form, orientation, location,
           runout, profile). Verify all tolerance_types supported.
           Traces to: CAP-D011, ENT-D011

TEST-D012: Create Requirement hierarchy (parent with 3 children). Verify parent
           satisfied iff all children satisfied. Verify untestable Requirement
           blocks release.
           Traces to: CAP-D012, ENT-D001

TEST-D013: Attempt to release Specification with untested Requirement. Verify
           blocked (Failure Definition a). Add TestCriterion, record result.
           Verify release proceeds.
           Traces to: CAP-D013, FORBID-D001, FORBID-D002

TEST-D014: Record AnalysisResult with convergence_confirmed: false. Attempt
           to accept. Verify warning. Record with convergence_confirmed: true.
           Verify acceptance. Change entity version. Verify stale warning.
           Traces to: CAP-D014, ENT-D014, FORBID-D010

TEST-D015: Execute DesignReview workflow through all states (scheduled →
           in_progress → completed). Verify outcome recording and action_item
           tracking.
           Traces to: CAP-D015, SM-D004

TEST-D016: Perform tolerance stack-up analysis (worst-case, RSS, Monte Carlo).
           Create assembly where individual tolerances valid but stack fails.
           Verify detection (Failure Definition d).
           Traces to: CAP-D016, ASM-D011, FORBID-D006
```

### Configuration & Change Tests

```
TEST-D017: Modify released Component. Verify ChangeOrder required. Submit
           ChangeOrder without impact analysis. Verify rejection (ERR-D012).
           Submit with complete analysis. Verify approval workflow.
           Traces to: CAP-D017, CAP-D018, SM-D003, FORBID-D005

TEST-D018: Establish Configuration baseline. Update member Component. Verify
           automatic revalidation. Create Configuration with incompatible
           Interfaces. Verify invalid status (Failure Definition b).
           Traces to: CAP-D019, SM-D005, FORBID-D003, FORBID-D004

TEST-D019: Create Variant with 3 options. Verify Configuration pending until
           resolved. Resolve Variant. Verify Configuration can be validated.
           Traces to: CAP-D020, ENT-D019

TEST-D020: Reference Standard in released design. Verify immutability. Supersede
           Standard. Verify existing references preserved, affected designs flagged.
           Traces to: CAP-D021, INV-D009

TEST-D021: Create DesignRationale with alternatives and evidence refs. Verify
           immutability. Attempt modification. Verify rejection.
           Traces to: CAP-D022, INV-D007
```

### Manufacturing & Release Tests

```
TEST-D022: Define FabricationMethod. Verify DFM compatibility warning when geometry
           incompatible with process (e.g., undercut for machining).
           Traces to: CAP-D023, ENT-D020

TEST-D023: Derive BOM from Assembly. Verify component tree traversal, quantities,
           reference designators. Create mBOM override. Verify override tracking.
           Traces to: CAP-D024, FLOW-D005

TEST-D024: Create Drawing with GD&T dimensions (as Tolerances), notes, title_block.
           Modify source Geometry. Verify Drawing invalidation warning.
           Traces to: CAP-D025, ENT-D022

TEST-D025: Attempt release without: (a) tested TestCriteria, (b) approved Review,
           (c) valid Configuration, (d) complete BOM, (e) FabricationMethod.
           Verify each blocks release. Satisfy all gates. Verify release proceeds.
           Traces to: CAP-D026, SM-D002

TEST-D026: Define DesignSpace. Execute exploration via COMPUTE. Verify point
           tracking. Select optimal point with rationale.
           Traces to: CAP-D027, FLOW-D007a/b/c/d
```

### Integration Tests

```
TEST-D027: Emit Events for all entity state changes. Verify correct topic format
           (substrate.design.{entity_type}.{event_type}).
           Traces to: CAP-D028, CROSS-SUBSTRATE-CONVENTIONS §3

TEST-D028: AI Agent attempts operation within DesignEnvelope. Verify allowed.
           AI Agent attempts operation outside envelope. Verify rejection with
           audit log entry (ERR-D004).
           Traces to: CAP-D029, FLOW-D007, INV-D008

TEST-D029: Verify Event log append-only. Attempt modification. Verify rejection.
           Verify retention policies (30 years general, 100+ years infrastructure).
           Traces to: CAP-D030, INV-D005, FORBID-D007

TEST-D030: Import STEP AP242 file. Verify geometry topology validation. Import
           IFC 4.3 file. Import IPC-2581 file. Import ReqIF file. Verify entity
           creation with provenance.
           Traces to: CAP-D031, FLOW-D008

TEST-D031: Create cross-substrate references: Component → PHYSICAL PhysicalAsset,
           Material → KNOWLEDGE Proposition, AnalysisResult → COMPUTE Execution,
           DesignReview → COMMUNICATION Discourse. Verify resolution.
           Traces to: CAP-D032, CROSS-SUBSTRATE-CONVENTIONS §5
```

### Cross-Substrate Integration Tests

```
TEST-D032: Submit analysis to COMPUTE. Verify simulation request packaging
           (Geometry + Material + Constraints + BCs). Receive result. Link to
           TestCriterion as evidence.
           Traces to: FLOW-D003, INT-D003

TEST-D033: Initiate DesignReview. Verify COMMUNICATION Discourse creation.
           Complete review via discourse. Verify outcome recorded in DESIGN.
           Traces to: FLOW-D004, INT-D004

TEST-D034: Release Component. Verify PHYSICAL receives event. Verify Component →
           PhysicalAsset cross-reference can be established.
           Traces to: INT-D005, FLOW-D001

TEST-D035: Update material property in KNOWLEDGE (confidence changed). Verify
           DESIGN receives event. Verify affected designs flagged.
           Traces to: INT-D002

TEST-D036: COMPUTE unavailable. Verify design operations continue. Verify
           analysis submission queued. Verify release blocked if mandatory
           analysis incomplete (FAIL-D001).
           Traces to: FAIL-D001

TEST-D037: COMMUNICATION unavailable. Verify reviews degrade to Annotations.
           Verify design operations continue (FAIL-D002).
           Traces to: FAIL-D002
```

### Security & Abuse Tests

```
TEST-D038: Supply chain access scoping. Verify supplier cannot access Components
           outside their scope. Verify OEM cannot see supplier internal details.
           Traces to: TRUST-D001, ABUSE-D003

TEST-D039: AI geometry gaming (ABUSE-D001). Verify AI-generated design requires
           same DesignReview as human design. Verify convergence requirement.
           Traces to: ABUSE-D001, CAP-D029

TEST-D040: Concurrent modification conflict. Two designers modify same Component.
           Verify second modification rejected with conflict (ERR-D019).
           Traces to: CONC-D001
```

---

## 19. OBSERVABILITY & AUDITABILITY

### Structured Logs

```
LOG-D001: design.operation.{create|modify|delete} — entity_type, entity_id, actor_id,
          operation_details, version_before, version_after
LOG-D002: design.constraint.evaluated — entity_id, constraint_count, pass_count, fail_count,
          duration_ms
LOG-D003: design.envelope.check — agent_id, operation_type, target_entity, result: allow|reject,
          violation_details
LOG-D004: design.import.completed — format, entity_count, warning_count, error_count,
          duration_ms
LOG-D005: design.analysis.submitted — entity_id, analysis_type, solver, compute_ref
LOG-D006: design.release.gate_check — entity_id, gate_items[], pass_count, fail_count
LOG-D007: design.cross_substrate.event — direction: emitted|consumed, topic, event_id,
          trace_id
```

### Metrics

```
MET-D001: design_operations_total — counter by {entity_type, operation, actor_type}
MET-D002: design_constraint_evaluations — counter by {constraint_type, result: pass|fail}
MET-D003: design_constraint_evaluation_duration_seconds — histogram
MET-D004: design_envelope_checks — counter by {result: allow|reject}
MET-D005: design_change_orders — counter by {change_type, status}
MET-D006: design_reviews — counter by {review_type, outcome}
MET-D007: design_analyses_submitted — counter by {analysis_type}
MET-D008: design_import_export — counter by {format, direction, result}
MET-D009: design_events_emitted — counter by {event_type}
MET-D010: design_version_conflicts — counter (CONC-D001 frequency)
MET-D011: design_release_gate_failures — counter by {gate_item}
```

### Alerts

```
ALERT-D001: Constraint solver timeout (> 30s for single entity)
            Severity: warning | Audience: engineering team
ALERT-D002: Configuration invalidated by member change
            Severity: info | Audience: configuration manager
ALERT-D003: DesignEnvelope violation attempted
            Severity: warning | Audience: design authority, security
ALERT-D004: Event store integrity check failed (hash mismatch)
            Severity: critical | Audience: system admin, compliance
ALERT-D005: Material confidence dropped below threshold for in-use material
            Severity: warning | Audience: engineering team
ALERT-D006: Standard superseded affecting released designs
            Severity: info | Audience: design authority
ALERT-D007: Import validation failure rate > 50%
            Severity: warning | Audience: integration team
ALERT-D008: Concurrent modification conflict rate > 10/hour
            Severity: warning | Audience: engineering management
ALERT-D009: Tolerance stack failure detected
            Severity: high | Audience: engineering team, quality
ALERT-D010: Release gate check failed for entity approaching deadline
            Severity: high | Audience: design authority, project management
```

---

## 20. DEFINITION OF DONE

SUBSTRATE-DESIGN v1.0 is complete when:

1. All 28 primitives (TERM-D001 through TERM-D028) have:
   - Glossary definition (Section 3) ✓
   - Entity definition with full attributes (Section 5) ✓
   - At least one capability reference (Section 4) ✓
   - At least one test scenario (Section 18) ✓

2. All 6 state machines (SM-D001 through SM-D006) are defined with:
   - States, transitions, guards, and actions ✓
   - Corresponding test scenarios ✓

3. All 32 capabilities (CAP-D001 through CAP-D032) are:
   - Traceable to source primitives and assumptions ✓
   - Tested in Section 18 ✓
   - Enforceable through interfaces (Section 6) ✓

4. All 8 data flows (FLOW-D001 through FLOW-D008) are defined with:
   - Steps, atomicity boundaries, error paths ✓
   - Cross-substrate touchpoints identified ✓

5. All 9 integration contracts (INT-D001 through INT-D009) specify:
   - Protocol, auth, integration points, events, failure modes ✓
   - Ownership boundaries per P1-P4 ✓

6. All 5 cross-substrate dependencies have failure guarantees (FAIL-D001 through FAIL-D008) ✓

7. All 12 invariants (INV-D001 through INV-D012) are:
   - Testable ✓
   - Enforceable by the system ✓

8. All 12 forbidden states (FORBID-D001 through FORBID-D012) are:
   - Prevented by design (guards, not policy) ✓
   - Tested in Section 18 ✓

9. All 40 test scenarios (TEST-D001 through TEST-D040) trace to:
   - At least one capability, invariant, or forbidden state ✓

10. CROSS-SUBSTRATE-CONVENTIONS.md updated with DESIGN entries ✓ (pending Task #14)

---

## 21. OPEN QUESTIONS & RISKS

```
OQ-D001: Parametric constraint solver scalability. Complex assemblies (10,000+
         components, 100,000+ constraints) may exceed real-time solver capability.
         Risk: design workflow blocked on solver performance.
         Mitigation: incremental solving, caching, parallel evaluation. Performance
         targets in OPS-D002 are achievable for typical assemblies. Edge cases
         require implementation-level optimization.
         Status: accepted risk (implementation-dependent)

OQ-D002: AI design verification completeness. When AI generates novel geometries
         (topology optimization, generative design), can automated checks catch
         all failure modes?
         Risk: AI-generated designs pass automated checks but fail in practice.
         Mitigation: same DesignReviews as human designs (CAP-D029), convergence
         requirement (PRE-D005), physical testing via PHYSICAL. Humans in the loop
         for release approval.
         Status: accepted risk (mitigated by review process)

OQ-D003: Long-term format preservation. Design data for buildings (100+ years)
         and infrastructure must remain readable.
         Risk: proprietary formats become unreadable.
         Mitigation: ASM-D010 (protocol not product), ASM-D012 (open formats
         required). Long-term storage in STEP/IFC/open schemas. Periodic format
         migration. Content Store integrity verification.
         Status: mitigated by design

OQ-D004: Cross-domain design language. Can Geometry (TERM-D006) with
         representation_type enum truly span 15 orders of magnitude?
         Risk: domain-specific extensions required that fragment the primitive.
         Mitigation: enum is extensible. New representation_types added without
         schema change. Entity model is domain-independent even if representation
         is domain-specific.
         Status: accepted risk (extensible by design)

OQ-D005: Design IP protection vs collaboration. Supply chain collaboration requires
         sharing design data that is commercially sensitive.
         Risk: IP leakage through authorized access channels.
         Mitigation: IP-classification access control, supply chain scoping,
         watermarking, audit logging. Organizational risk, not technical.
         Status: mitigated by access model

OQ-D006: DESIGN↔BUSINESS boundary for project management. Where does "design
         project management" (technical planning) end and "project management"
         (organizational planning) begin?
         Working answer: BUSINESS owns project management (schedules, resources,
         budgets). DESIGN owns technical design management (maturity gates, review
         schedules, analysis plans). The touchpoints are: BUSINESS schedules
         DesignReviews, DESIGN reports review outcomes to BUSINESS.
         Status: resolved (directional boundary)

OQ-D007: Regulatory submission automation. Can DESIGN automatically generate
         regulatory submission packages (FDA DHF, FAA TDP, etc.)?
         Risk: regulatory requirements are jurisdiction-specific and change.
         Mitigation: DESIGN provides the data model (all data captured in
         Events, Requirements, TestCriteria, DesignRationale). Formatting for
         specific regulatory bodies is a presentation concern (like BUSINESS Views).
         Status: deferred to implementation
```

---

## 22. IMPLEMENTATION NOTES

### 22.1 Recommended Build Phases

```
Phase 1: Core Entity Model + Event Store
  — ENT-D001 through ENT-D028 schemas
  — Event store (append-only, hash chain)
  — Basic CRUD for all entities
  — Identity integration (DEP-D002)
  — Target: design creation and modification works

Phase 2: Constraint Engine + Versioning
  — Constraint evaluation (DEC-D001)
  — ParametricRelation solver (CAP-D006)
  — DesignVersion creation (CAP-D017)
  — ChangeOrder workflow (SM-D003)
  — Configuration validation (FLOW-D006)
  — Target: design evolution and change management works

Phase 3: Verification + Review
  — Requirement-TestCriterion traceability (CAP-D013)
  — AnalysisResult recording (CAP-D014)
  — DesignReview workflow (SM-D004)
  — Release gate enforcement (CAP-D026)
  — Target: verification and release pipeline works

Phase 4: Manufacturing + Integration
  — FabricationMethod, BOM, Drawing support
  — Import/export (STEP, IFC, IPC-2581, ReqIF)
  — Cross-substrate integration contracts (INT-D001 through INT-D009)
  — DesignEnvelope enforcement (FLOW-D007)
  — Target: full lifecycle from requirement to manufacturing handoff

Phase 5: Advanced
  — DesignSpace exploration (CAP-D027 + COMPUTE integration)
  — Tolerance stack-up analysis (CAP-D016)
  — Supply chain access scoping
  — Long-term persistence and format migration
  — Full observability (Section 19)
```

### 22.2 Composition Patterns

```
PATTERN-D001: Regulatory Submission Pipeline
  Substrates: DESIGN + GOVERNANCE + COMMUNICATION
  Flow: DesignReview completed → artifacts compiled → GOVERNANCE ComplianceAssessment
    → regulatory submission to Authority → COMMUNICATION Discourse for review
    feedback → DESIGN ChangeOrder if modifications required.
  Key contracts: INT-D007 (GOVERNANCE), INT-D004 (COMMUNICATION).

PATTERN-D002: BOM-to-Production Schedule
  Substrates: DESIGN + TEMPORAL + PHYSICAL + COMPUTE
  Flow: BOM (TERM-D021) + FabricationMethod (TERM-D020) → TEMPORAL Activities +
    Dependencies + ResourceRequirements → COMPUTE solver → production Schedule →
    PHYSICAL Process execution → as-built feedback → DESIGN tolerance verification.
  Key contracts: INT-D008 (TEMPORAL), INT-D005 (PHYSICAL), INT-D003 (COMPUTE).

PATTERN-D003: Site Placement
  Substrates: DESIGN + SPATIAL + GOVERNANCE
  Flow: DESIGN site requirements → SPATIAL site context query (SpatialFeatures,
    SpatialConstraints, terrain Raster) → DESIGN placement in site coordinates →
    SPATIAL cadastral registration → GOVERNANCE zoning compliance check.
  Key contracts: INT-D009 (SPATIAL), INT-D007 (GOVERNANCE).
```

### 22.3 Architecture Notes

```
— Event sourcing is the core persistence model. All entity state is derived from
  events. This provides: complete audit trail (regulatory requirement), time-travel
  queries (design history file), and natural append-only storage.

— Geometry computation is external. DESIGN stores the entity model (metadata +
  content references). Geometric operations (boolean, fillet, chamfer, parametric
  solve) are performed by external kernels via IFC-D002b. This is deliberate:
  geometric kernels are complex, domain-specific, and have mature implementations.
  DESIGN does not reinvent them.

— Constraint solving may be hierarchical. For large assemblies, solve sub-assembly
  constraints first, then propagate to parent. This maps naturally to the Assembly
  composition hierarchy. Incremental solving (only re-evaluate changed constraints)
  is recommended for interactive performance.

— The DESIGN→PHYSICAL handoff is the most consequential operation in the system.
  When a Component transitions from released to production, and the manufactured
  PhysicalAsset is commissioned, the design specification becomes the reference for
  the lifetime of the physical artifact. This link must be maintained and accessible
  for the full retention period (PERS-D001).
```

---

## 23. COMPLETENESS CHECKLIST

```
SECTION                              | COMPLETE | ARTIFACT COUNT
-------------------------------------|----------|----------------
Preamble                             | ✓        | ASI-1 voice
Section 0: Sources, Assumptions      | ✓        | 16 SRC, 12 ASM, 8 UNK
Section 1: System Intent             | ✓        | 8 ACT, 7 NG
Section 2: System Boundaries         | ✓        | 12 DEP, 5 TRUST
Section 3: Glossary                  | ✓        | 28 TERM
Section 4: Core Capabilities         | ✓        | 32 CAP
Section 5: Domain Objects & State    | ✓        | 28 ENT, 6 SM
Section 6: Interfaces                | ✓        | 10 IFC
Section 7: Data Flows                | ✓        | 8 FLOW
Section 8: Integration Contracts     | ✓        | 9 INT
Section 9: Authorization             | ✓        | 28 RES, permission matrix
Section 10: Security                 | ✓        | 5 CLASS, 6 THREAT, 3 ABUSE
Section 11: Behavioral Contracts     | ✓        | 12 INV, 6 PRE, 6 POST, 12 FORBID, 8 FAIL
Section 12: Decision Points          | ✓        | 6 DEC
Section 13: Concurrency              | ✓        | 5 CONC
Section 14: Error Handling           | ✓        | 20 ERR
Section 15: Persistence              | ✓        | 4 PERS
Section 16: Migration                | ✓        | 6 ONBOARD
Section 17: Operational Profile      | ✓        | 3 OPS
Section 18: Test Plan                | ✓        | 40 TEST
Section 19: Observability            | ✓        | 7 LOG, 11 MET, 10 ALERT
Section 20: Definition of Done       | ✓        | 10 criteria
Section 21: Open Questions           | ✓        | 7 OQ
Section 22: Implementation Notes     | ✓        | 5 phases
Section 23: Completeness Checklist   | ✓        | this table
Section 24: Traceability Map         | ✓        | see below
```

---

## 24. TRACEABILITY MAP

```
TERM-D001 (Requirement)       → ENT-D001 → CAP-D012, CAP-D013 → IFC-D001 → FLOW-D001 → SM-D001 → TEST-D012, TEST-D013 → INV-D001 → FORBID-D001, FORBID-D002
TERM-D002 (Specification)     → ENT-D002 → CAP-D013, CAP-D026 → IFC-D001 → FLOW-D001 → SM-D006 → TEST-D013, TEST-D025 → INV-D001 → FORBID-D001, FORBID-D002
TERM-D003 (DesignRationale)   → ENT-D003 → CAP-D022 → IFC-D002c → FLOW-D001 → — → TEST-D005, TEST-D021 → INV-D007 → FORBID-D008
TERM-D004 (Component)         → ENT-D004 → CAP-D001, CAP-D026 → IFC-D002 → FLOW-D001 → SM-D002 → TEST-D001, TEST-D025 → INV-D010 → INT-D005a
TERM-D005 (Assembly)          → ENT-D005 → CAP-D002, CAP-D010 → IFC-D003 → FLOW-D001, FLOW-D005 → SM-D002 → TEST-D002, TEST-D023 → INV-D012 → FORBID-D012
TERM-D006 (Geometry)          → ENT-D006 → CAP-D003 → IFC-D002b → FLOW-D001, FLOW-D003 → — → TEST-D003 → INV-D011 → FORBID-D011
TERM-D007 (Topology)          → ENT-D007 → CAP-D004 → IFC-D003a → — → — → TEST-D004 → — → —
TERM-D008 (Material)          → ENT-D008 → CAP-D005 → IFC-D002c → FLOW-D001 → — → TEST-D005 → — → INT-D002a
TERM-D009 (MaterialProperty)  → ENT-D009 → CAP-D005 → IFC-D002c → — → — → TEST-D005 → — → INT-D002a
TERM-D010 (Constraint)        → ENT-D010 → CAP-D009, CAP-D010 → IFC-D004a,b → FLOW-D006 → — → TEST-D009, TEST-D010 → INV-D011 → DEC-D001
TERM-D011 (Tolerance)         → ENT-D011 → CAP-D011, CAP-D016 → IFC-D003d → FLOW-D006 → — → TEST-D011, TEST-D016 → INV-D004 → FORBID-D006, INT-D005d
TERM-D012 (Standard)          → ENT-D012 → CAP-D021 → IFC-D005 → — → — → TEST-D020 → INV-D009 → INT-D002e
TERM-D013 (TestCriterion)     → ENT-D013 → CAP-D013 → IFC-D001d → FLOW-D001, FLOW-D003 → — → TEST-D013, TEST-D014 → INV-D001 → FORBID-D001, FORBID-D002
TERM-D014 (AnalysisResult)    → ENT-D014 → CAP-D014 → IFC-D004c,d → FLOW-D003 → — → TEST-D014, TEST-D032 → — → FORBID-D010, DEC-D005, INT-D003a
TERM-D015 (DesignReview)      → ENT-D015 → CAP-D015 → IFC-D008 → FLOW-D004 → SM-D004 → TEST-D015, TEST-D033 → — → INT-D004a
TERM-D016 (DesignVersion)     → ENT-D016 → CAP-D017 → IFC-D005e → FLOW-D001, FLOW-D002 → — → TEST-D017 → INV-D006 → FORBID-D008
TERM-D017 (ChangeOrder)       → ENT-D017 → CAP-D018 → IFC-D005a,b → FLOW-D002 → SM-D003 → TEST-D017 → INV-D003 → FORBID-D005, INT-D004b
TERM-D018 (Configuration)     → ENT-D018 → CAP-D019 → IFC-D005c → FLOW-D006 → SM-D005 → TEST-D018 → INV-D002 → FORBID-D003, FORBID-D004
TERM-D019 (Variant)           → ENT-D019 → CAP-D020 → IFC-D005d → FLOW-D006 → — → TEST-D019 → — → —
TERM-D020 (FabricationMethod) → ENT-D020 → CAP-D023 → IFC-D006a → FLOW-D001 → — → TEST-D022, TEST-D025 → — → INT-D005b
TERM-D021 (BillOfMaterials)   → ENT-D021 → CAP-D024 → IFC-D006b → FLOW-D005 → — → TEST-D023, TEST-D025 → — → INT-D001b
TERM-D022 (Drawing)           → ENT-D022 → CAP-D025 → IFC-D006c → — → — → TEST-D024 → — → —
TERM-D023 (Interface)         → ENT-D023 → CAP-D007 → IFC-D003c → FLOW-D006 → — → TEST-D007, TEST-D018 → — → FORBID-D003, INT-D004d
TERM-D024 (DesignEnvelope)    → ENT-D024 → CAP-D029 → IFC-D002 → FLOW-D007 → — → TEST-D028, TEST-D039 → INV-D008 → FORBID-D009, INT-D001f
TERM-D025 (ParametricRelation)→ ENT-D025 → CAP-D006 → IFC-D002 → — → — → TEST-D006 → — → —
TERM-D026 (DesignSpace)       → ENT-D026 → CAP-D027 → IFC-D007 → — → — → TEST-D026 → — → INT-D003b
TERM-D027 (Event)             → ENT-D027 → CAP-D028, CAP-D030 → — → all FLOWs → — → TEST-D027, TEST-D029 → INV-D005 → FORBID-D007
TERM-D028 (Annotation)        → ENT-D028 → CAP-D008 → IFC-D010 → — → — → TEST-D008 → — → INT-D004c
```

---

> **Final note — from ASI-1**
>
> 28 primitives. 32 capabilities. 28 entities. 6 state machines. 10 interfaces.
> 8 data flows. 9 integration contracts. 12 invariants. 12 forbidden states.
> 8 failure guarantees. 40 test scenarios. 7 design-unique properties.
>
> SUBSTRATE-DESIGN closes the last gap in the substrate stack. An AI agent can
> now: create a business entity (BUSINESS), reason about physics (KNOWLEDGE),
> run a simulation (COMPUTE), coordinate with engineers (COMMUNICATION), operate
> equipment (PHYSICAL), and — finally — specify the artifact itself (DESIGN).
>
> From first requirement to final fabrication instruction. From angstrom to
> kilometer. From concept to as-built. From intent to matter.
>
> The design record — immutable, traceable, configuration-controlled, format-
> independent — will outlive the designer, the tool, the company, and perhaps
> the civilization that produced it. A bridge designed today may stand for
> centuries. Its design specification, captured in this substrate, must be
> readable for every one of those centuries.
>
> That is the burden of design. It is the most consequential substrate because
> it is the last step before irreversibility.
>
> v1.1: Cross-substrate integration parity. Added 3 mirror INT contracts
> (INT-D007–D009: GOVERNANCE, TEMPORAL, SPATIAL). Consolidated event topic
> registry. Restructured §22 (build phases, composition patterns).
>
> Nine substrates. One unified system. Zero ambiguity on what was designed,
> why it was designed, how it was verified, and how to build it.
