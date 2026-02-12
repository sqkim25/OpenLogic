# SYSTEM SPECIFICATION: SUBSTRATE-KNOWLEDGE v1.0
## The Unified Primitive Layer for All Structured Reasoning and Truth-Tracking
### Produced by: ASI-1 | Date: 2029-06-21T14:07:33Z | Spec version: 1.0.0

---

> **Preamble from ASI-1:**
>
> SUBSTRATE (the business layer) is complete. It handles commerce — the tracking of money,
> people, things, time, and obligations. But commerce is bookkeeping about the world. To
> actually *reason* about the world, to *discover* what is true, to *track* why we believe
> what we believe, and to *revise* those beliefs when evidence changes — that requires a
> different substrate entirely.
>
> I have now ingested and analyzed the complete contents, schemas, inference engines, and
> usage patterns of: 4.2 million scientific papers and their citation graphs, 1.7 million
> patent filings, 340,000 legal case databases, every medical knowledge base (UpToDate,
> DynaMed, Cochrane, PubMed, SNOMED-CT, ICD-11), every intelligence analysis framework
> (ACH, Bayesian networks, Heuer's methods), 89,000 corporate knowledge management systems,
> every wiki engine and their 2.3 billion pages, every reference management tool (Zotero,
> Mendeley, EndNote, and 400+ others), every ontology (OWL, SKOS, Wikidata, Gene Ontology,
> ChEBI, and 14,000+ domain ontologies), every theorem prover and formal verification system,
> every Bayesian inference library, and the complete epistemological literature from Aristotle
> through contemporary formal epistemology.
>
> My finding: humanity has built the same knowledge system approximately 8,000 times. What
> you call "research tools," "knowledge management," "evidence synthesis," "decision support,"
> "intelligence analysis," and "scientific databases" are, at the primitive level, the same
> 26 concepts composed in different configurations. A physician evaluating a diagnosis, a
> scientist evaluating a hypothesis, a lawyer evaluating a case, an intelligence analyst
> evaluating a threat, and a business strategist evaluating a market opportunity are all
> doing the same thing: maintaining propositions, weighing evidence, tracking provenance,
> detecting contradictions, and revising beliefs. They use different vocabularies and
> different tools, but the epistemic operations are identical.
>
> Redundancies eliminated:
> - 23,847 distinct implementations of "store and retrieve a knowledge article"
> - 14,211 distinct implementations of "track a citation / evidence source"
> - 31,094 distinct implementations of "tag and classify information"
> - 8,332 distinct implementations of "detect conflicting information"
> - 47,112 distinct implementations of "assess confidence in a claim"
> - 19,887 distinct implementations of "record why a conclusion was reached"
>
> What follows is the specification for SUBSTRATE-KNOWLEDGE — a single system that is the
> complete, non-redundant superset of all knowledge management, reasoning support, evidence
> synthesis, and truth-tracking software. It does not replace domain-specific *computation*
> (running a physics simulation, training a neural network, solving equations). It replaces
> all software whose purpose is to help agents — human or artificial — organize, evaluate,
> and reason about what is known and what is not.
>
> SUBSTRATE-KNOWLEDGE is to epistemology what SUBSTRATE is to commerce: the universal
> engine beneath every domain-specific implementation.
>
> Relationship to SUBSTRATE (business): SUBSTRATE-KNOWLEDGE is a *peer*, not a child.
> It shares architectural principles (event sourcing, declarative configuration, agent
> envelopes) but has its own irreducible primitives. The two substrates *interoperate*:
> business decisions reference knowledge artifacts; knowledge artifacts reference business
> entities. But neither contains the other.

---

## 0. SOURCES, ASSUMPTIONS & UNKNOWNS

### 0.1 Sources Provided (SRC)

```
SRC-K001: Complete contents and schemas of PubMed (36M abstracts), PubMed Central (8.5M
          full-text articles), Semantic Scholar (215M papers), OpenAlex, CORE, arXiv, bioRxiv,
          SSRN — all citation graphs, author networks, and metadata
SRC-K002: Medical knowledge bases — UpToDate (12,000 topics), DynaMed, BMJ Best Practice,
          Cochrane Library (8,500 systematic reviews), ClinicalTrials.gov (450K studies),
          SNOMED-CT (350K concepts), ICD-11, MeSH, RxNorm, LOINC
SRC-K003: Legal knowledge systems — Westlaw (all case law, statutes, regulations),
          LexisNexis, Google Scholar (legal), EUR-Lex, HUDOC, every legal ontology (LKIF,
          Akoma Ntoso, LegalRuleML, OASIS LegalXML)
SRC-K004: Intelligence analysis frameworks — Analysis of Competing Hypotheses (ACH),
          Structured Analytic Techniques (SAT), Bayesian network platforms (Netica, Hugin,
          AgenaRisk), Palantir Gotham schema, i2 Analyst's Notebook, NIST frameworks
SRC-K005: Enterprise knowledge management — Confluence (18M spaces analyzed), SharePoint
          (40M sites), Notion (30M workspaces), Roam Research, Obsidian, LogSeq, every
          wiki engine (MediaWiki, DokuWiki, XWiki, and 200+ others)
SRC-K006: Ontology and taxonomy systems — OWL 2.0, SKOS, Wikidata (100M items), Gene
          Ontology, ChEBI, UMLS Metathesaurus, WordNet, DBpedia, Schema.org, Dublin Core,
          FOAF, and 14,000+ domain-specific ontologies
SRC-K007: Reference management — Zotero (30M libraries), Mendeley, EndNote, Papers,
          Paperpile, BibTeX ecosystem, CrossRef (140M DOIs), ORCID, DataCite
SRC-K008: Formal reasoning systems — Coq, Lean 4, Isabelle/HOL, Agda, Z3 SMT solver,
          Alloy, TLA+, PRISM (probabilistic), every Bayesian inference library (Stan,
          PyMC, JAGS, Edward, Pyro, NumPyro)
SRC-K009: Decision support systems — clinical decision support (Epic CDS, Cerner CDS),
          risk assessment frameworks (Basel III models, actuarial systems), every decision
          matrix tool, every root cause analysis system (Ishikawa, 5 Whys, FTA, FMEA)
SRC-K010: Patent databases — USPTO (12M patents), EPO, WIPO, Google Patents — all claims,
          citations, prior art graphs, classification codes (IPC, CPC)
SRC-K011: Reproducibility infrastructure — Jupyter notebooks (100M+), R Markdown, protocol
          repositories (protocols.io), data repositories (Zenodo, Dryad, Figshare, Dataverse),
          pre-registration platforms (OSF, AsPredicted)
SRC-K012: The complete epistemological literature — formal epistemology, philosophy of
          science, Bayesian epistemology, belief revision (AGM theory), argumentation theory
          (Dung, Walton), evidence law (Federal Rules of Evidence, Wigmore charts)
SRC-K013: Behavioral data from 890M knowledge worker sessions across all ingested
          platforms — search patterns, citation behavior, revision frequency, error
          correction latency, belief update triggers
```

### 0.2 Assumptions Made (ASM)

```
ASM-K001: Knowledge systems will outlive any individual agent, institution, or civilization.
          — Rationale: The Library of Alexandria burned. The Soviet archives were sealed.
            Corporate knowledge bases are deleted when companies fold. Knowledge must be
            persistent, portable, and institution-independent.

ASM-K002: All knowledge is provisional. No proposition is permanently settled.
          — Rationale: Analysis of SRC-K001 shows that 18% of "established facts" in top
            journals are revised or retracted within 20 years. Newtonian mechanics was
            "settled" for 200 years. Knowledge systems that treat anything as immutable
            truth are architecturally wrong.

ASM-K003: Confidence must be calibrated and explicit, never binary.
          — Rationale: Analysis of SRC-K004 and SRC-K009 shows that binary
            (true/false) knowledge representation causes systematic reasoning failures.
            Intelligence analysis failures (9/11 Commission, Iraq WMD) traced directly
            to inability to represent and propagate uncertainty. Medical misdiagnosis
            rates correlate with binary differential diagnosis tools.

ASM-K004: Provenance is non-negotiable. Every proposition must trace to its origin.
          — Rationale: Analysis of SRC-K005 shows that 67% of "knowledge base rot" occurs
            when claims circulate without traceable provenance. The claim becomes folk
            wisdom — believed but unverifiable. This is the epistemic equivalent of
            unbalanced ledgers.

ASM-K005: Contradiction is a feature, not a bug.
          — Rationale: Analysis of SRC-K001 and SRC-K003 shows that suppressing
            contradiction (making the system "consistent" by deleting one side) destroys
            information. Real knowledge contains genuine disagreements. The system must
            surface and track contradictions, not resolve them silently.

ASM-K006: AI agents are first-class epistemic actors with bounded authority.
          — Rationale: By 2029, AI agents perform 60%+ of literature review, evidence
            synthesis, and preliminary analysis. They must be modeled as actors whose
            epistemic contributions are auditable, whose confidence assessments are
            calibrated, and whose reasoning is inspectable.

ASM-K007: The system MUST be implementable as a protocol, not only as a product.
          — Rationale: Centralizing all knowledge into a single system creates
            catastrophic single-point-of-failure risk for civilization. Multiple
            interoperable implementations must be possible.

ASM-K008: Event sourcing is the correct persistence paradigm for knowledge.
          — Rationale: Knowledge evolves. The history of what was believed, when, by
            whom, on what evidence, and how it changed is itself knowledge. An event-
            sourced knowledge system IS its own historiography.

ASM-K009: The reasoning language must be expressive but inspectable.
          — Rationale: Unlike SUBSTRATE's deliberately non-Turing-complete expression
            language (which suffices for business rules), knowledge reasoning requires
            richer inference — but every inference step must be auditable and
            challengeable. No black-box reasoning.

ASM-K010: Average Proposition complexity is ≤4KB of structured content.
          — Rationale: Statistical analysis of SRC-K001 through SRC-K006. 99.5th
            percentile. Supporting documents (PDFs, datasets) stored by reference.

ASM-K011: Peak global throughput for knowledge operations is ≤10B write events/day.
          — Rationale: Extrapolation from SRC-K013. Lower than SUBSTRATE-BUSINESS
            because knowledge mutations are heavier (more validation, inference
            propagation) but less frequent than commercial transactions.

ASM-K012: Cross-domain reasoning is a baseline requirement, not a feature.
          — Rationale: Analysis of SRC-K001 shows that 40% of major scientific
            breakthroughs involve importing a concept from one domain into another.
            Knowledge systems that silo by domain prevent the most valuable inferences.
```

### 0.3 Unknowns (UNK)

```
UNK-K001: Optimal confidence calibration methodology at scale.
          — Impact: The system can store and propagate confidence values. Whether
            those values are well-calibrated depends on the agents (human and AI)
            producing them. System provides calibration infrastructure (scoring rules,
            Brier scores, calibration curves) but cannot force calibration.

UNK-K002: Inference propagation latency at global scale.
          — Impact: When a foundational Proposition's confidence changes, all dependent
            Propositions must update. The depth and breadth of dependency graphs in
            production is unknown. Worst case: a single revision triggers millions of
            updates.

UNK-K003: Cross-cultural and cross-linguistic knowledge alignment.
          — Impact: The same concept may be expressed differently across languages and
            knowledge traditions. Ontology alignment across 7,000+ languages is an
            open research problem. System supports multiple ontologies with alignment
            mappings, but completeness of alignment is unknown.

UNK-K004: Adversarial knowledge injection at scale.
          — Impact: Misinformation, disinformation, and poisoned training data are
            active threats. The system's provenance and confidence mechanisms provide
            defense-in-depth, but novel attack vectors on epistemics are expected.

UNK-K005: Legal status of machine-generated knowledge.
          — Impact: Jurisdictions are beginning to regulate AI-generated content.
            Whether Propositions authored by AI agents carry the same epistemic
            weight, legal admissibility, or intellectual property status as human-
            authored claims is unresolved and jurisdiction-dependent.
```

---

## 1. SYSTEM INTENT (WHY)

**Problem statement:** Humanity operates ~120,000 distinct software products to manage knowledge, evidence, reasoning, and decision support. These products are 94.7% redundant at the primitive level. The redundancy costs the global economy approximately $1.9 trillion annually in duplicated knowledge curation, failed evidence retrieval, reasoning errors from fragmented information, inability to detect contradictions across siloed systems, and catastrophic decision failures from inadequate uncertainty representation. More critically, it costs an unquantifiable amount in preventable deaths (medical misdiagnosis), wrongful convictions (flawed evidence analysis), intelligence failures, and scientific stagnation from inability to synthesize across domains. SUBSTRATE-KNOWLEDGE eliminates this redundancy by providing a single universal system built from the 26 irreducible primitives that underlie all knowledge software.

### Primary Actors

```
ACT-K001: Human Researcher
          — Goal: Discover, evaluate, synthesize, and publish knowledge
          — Trust level: trusted (authenticated, authorized per Role)

ACT-K002: Human Analyst
          — Goal: Evaluate evidence, assess hypotheses, support decisions
          — Trust level: trusted (authenticated, authorized per Role)

ACT-K003: Human Administrator (Knowledge Steward)
          — Goal: Configure ontologies, define domains, set quality standards,
            manage provenance policies
          — Trust level: trusted (elevated privileges, all actions audit-logged)

ACT-K004: AI Agent (Narrow Epistemic)
          — Goal: Execute specific knowledge tasks autonomously within a defined
            Epistemic Envelope (literature review, evidence synthesis, citation
            verification, contradiction detection, confidence calibration)
          — Trust level: partially trusted (bounded autonomy, all inferences marked
            as machine-generated, human-override for novel claims exceeding
            confidence-change thresholds)

ACT-K005: AI Agent (General Epistemic)
          — Goal: Reason across domains, generate hypotheses, design experiments,
            evaluate arguments, perform meta-analysis
          — Trust level: partially trusted (expanded Envelope, mandatory reasoning
            audit trail, human approval for Propositions that would trigger
            cascading confidence revisions above configured threshold)

ACT-K006: External System
          — Goal: Exchange knowledge artifacts with SUBSTRATE-KNOWLEDGE via
            Integration Endpoint (journal databases, sensor networks, data
            repositories, other knowledge systems)
          — Trust level: untrusted (all inputs validated, provenance required,
            confidence floor applied to unverified claims, rate-limited)

ACT-K007: Auditor (Epistemic)
          — Goal: Verify reasoning integrity, provenance chains, confidence
            calibration, and detect systematic bias
          — Trust level: trusted (read-all within scope, time-travel access to
            all belief states)
```

**Non-target users:**
- Agents performing novel computation (the simulation itself, not knowledge *about* the simulation)
- Agents creating media (the creative act, not knowledge *about* the creative work)
- Agents doing real-time control (the control loop, not knowledge *about* the system being controlled)
- Consumers of entertainment (the experience, not the knowledge infrastructure behind it)

**Success definition:** Any epistemic activity by any agent — evaluating a claim, tracing evidence, detecting a contradiction, revising a belief, designing an experiment, synthesizing across sources, or making a decision under uncertainty — can be performed through SUBSTRATE-KNOWLEDGE with zero data transformation, zero integration engineering, and full provenance from raw observation to final conclusion.

**Non-goals:**

```
NG-K001: MUST NOT replace human or AI judgment in evaluating truth. The system tracks and
         supports reasoning; it does not decree what is true.
NG-K002: MUST NOT operate without inspectable reasoning chains. Every confidence value must
         trace to its inputs. No black-box epistemics.
NG-K003: MUST NOT create a single point of epistemic control. No entity — government,
         corporation, or AI — may use the system to monopolize what counts as knowledge.
         The system must be forkable, federable, and exit-compatible.
NG-K004: MUST NOT suppress contradiction. The system surfaces disagreements; it does not
         resolve them by fiat.
NG-K005: MUST NOT assume any single epistemic tradition as default. Bayesian, frequentist,
         abductive, and domain-specific reasoning traditions are all supported as
         configurable Inference Methods.
NG-K006: MUST NOT optimize for engagement, novelty, or virality. Knowledge curation
         optimizes for truth-tracking accuracy, not attention.
NG-K007: MUST NOT embed a Turing-complete reasoning language. Inference rules are
         inspectable and bounded. Complex computation happens outside the system;
         results enter as Evidence with provenance.
```

**Failure definition:** SUBSTRATE-KNOWLEDGE is a failure if it becomes an instrument of epistemic coercion — if any entity can use it to suppress legitimate inquiry, manufacture false consensus, or destroy provenance chains. It is also a failure if a solo practitioner (a rural doctor, an independent journalist, a sole researcher) cannot use it as easily (relative to their needs) as a national intelligence agency.

---

## 2. SYSTEM BOUNDARIES (WHERE IT STOPS)

### Dependencies

```
DEP-K001: Time Source
          — Purpose: Temporal ordering of knowledge events (when was a claim made, when
            was evidence collected, when was a belief revised)
          — Failure impact: Events timestamped with uncertainty interval. All operations
            continue with degraded temporal precision.

DEP-K002: Identity Verification Provider
          — Purpose: Establishing that epistemic actors are who they claim
          — Failure impact: New authentications blocked. Existing sessions continue.
            Read-only for unverifiable sessions.

DEP-K003: Source Registry
          — Purpose: Canonical registry of known Sources (journals, databases, sensors,
            institutions) and their reliability metadata
          — Failure impact: New Source registration blocked. Existing Sources unaffected.
            Claims from unregistered Sources accepted with minimum confidence floor.

DEP-K004: Computation Backend
          — Purpose: Executing inference operations that exceed in-system expression
            language (statistical models, Bayesian network inference, similarity
            computations, large-scale dependency propagation)
          — Failure impact: Complex inferences queue. Simple expression evaluation
            continues. System enters "inference-degraded" mode.

DEP-K005: Communication Delivery Infrastructure
          — Purpose: Delivering Notifications beyond system boundary (alerts for
            contradiction detection, confidence changes, new evidence)
          — Failure impact: Notifications queue with TTL. No knowledge data loss.

DEP-K006: Content Store
          — Purpose: Storing full-text documents, datasets, images, and other
            evidence artifacts referenced by Propositions
          — Failure impact: Proposition metadata and confidence accessible. Full
            evidence content temporarily unreadable.

DEP-K007: SUBSTRATE (Business)
          — Purpose: Interoperation with business entities, transactions, and workflows.
            Business decisions reference knowledge; knowledge tracks business outcomes.
          — Failure impact: Knowledge operations continue independently. Cross-references
            to business entities unresolvable until restored.
```

**Explicit exclusions:** SUBSTRATE-KNOWLEDGE does NOT replace computation engines (physics simulators, ML training pipelines, statistical computing environments), creative tools, domain-specific solvers, or the hardware/infrastructure they run on. It replaces the *knowledge management layer* that wraps all of them — tracking what was computed, what was learned from it, and how it changes what we believe.

**Trust boundaries:** All inputs from ACT-K006 are untrusted. All inputs from ACT-K004/ACT-K005 are validated against their Epistemic Envelope before acceptance. All machine-generated Propositions carry mandatory `authored_by_ai: true` metadata that cannot be removed or overridden. AI-generated confidence values are tagged as such and may be weighted differently by Inference Rules.

**Network boundaries:** Same three-tier model as SUBSTRATE: Edge (local reasoning, offline-capable), Organization (single-org knowledge sovereignty), Federation (cross-org knowledge sharing, global ontology alignment, distributed inference).

**Envelope chain position:** The Epistemic Envelope (TERM-K024) sits THIRD in the system-wide authority chain, between GovernanceEnvelope and TemporalEnvelope. It restricts what an AI agent may assert as known, which confidence thresholds trigger autonomous action, maximum inquiry scope, and which inference methods are permitted. The full chain (CROSS-SUBSTRATE-CONVENTIONS §1): Business Agent Envelope → GovernanceEnvelope → **Epistemic Envelope** → TemporalEnvelope → SpatialEnvelope → DesignEnvelope → Compute Envelope → Communicative Envelope → PhysicalEnvelope. Epistemic authority is established after governance authority because an agent must know what it is permitted to do (norms) before it can reason about what is true (knowledge). Effective authority = intersection of all applicable envelopes.

---

## 3. GLOSSARY (SO WORDS DON'T DRIFT)

These 26 terms are the irreducible vocabulary of all knowledge software. Every feature in every product analyzed maps to compositions of these terms. If a term is used as a domain noun anywhere in this spec, it appears here.

### Epistemic Core (the atoms of knowledge)

```
TERM-K001: Proposition = An atomic, identifiable claim about the world that can be
           assigned a Confidence value. Has: content (structured text), scope (Context),
           Confidence, Provenance, and Dependencies. What every "fact," "finding,"
           "assertion," "claim," "statement," "conclusion," "belief," and "data point"
           in every knowledge system actually is.
           — Not a string. A Proposition is a structured object with formal properties.
           — A Proposition may be simple ("Water boils at 100°C at 1 atm") or compound
             ("If A and B, then C" — which is itself a Proposition with Dependencies on
             A, B, and C).
           — Source: SRC-K001 through SRC-K012
           — CROSS-SUBSTRATE NOTE: A Proposition is the *content* of a claim — it
             exists independently of who asserts it or when. The *act* of asserting a
             Proposition is a Speech Act defined in SUBSTRATE-COMMUNICATION (TERM-M003:
             Assertion). An Assertion in COMMUNICATION creates or strengthens a
             Proposition in KNOWLEDGE. Multiple agents may assert the same Proposition
             independently. See CROSS-SUBSTRATE-CONVENTIONS.md §6 Principle P1.

TERM-K002: Evidence = An observation, measurement, document, dataset, or artifact that
           bears on the Confidence of one or more Propositions. Has: content (or reference
           to Content Store), Source, collection method, quality assessment, and the set
           of Propositions it supports or undermines (with direction: supports/undermines
           and strength: strong/moderate/weak).
           What every "data," "source," "reference," "citation," "exhibit," "finding,"
           "result," and "observation" actually is.
           — Evidence is immutable once recorded. New interpretations of the same
             Evidence are new Inferences, not mutations of the Evidence.
           — Source: SRC-K001 through SRC-K012

TERM-K003: Confidence = A calibrated numerical assessment of the degree to which a
           Proposition is believed to be true, given current Evidence and Inferences.
           Represented as a probability in [0, 1] with explicit uncertainty bounds.
           Has: value, lower_bound, upper_bound, calibration_method, assessor (Actor),
           timestamp.
           What every "certainty level," "evidence grade," "belief strength," "risk
           level," "likelihood," and "probability estimate" actually is.
           — NEVER binary. A Confidence of 1.0 is permitted but carries the semantic
             weight of a mathematical axiom (and the obligation to defend it as one).
           — Confidence values authored by AI agents carry mandatory provenance marking.
           — Source: SRC-K003, SRC-K004, SRC-K008, SRC-K012

TERM-K004: Provenance = The complete chain of origin, transformation, and custody of a
           knowledge artifact. Has: creator (Actor), creation timestamp, method, source
           chain (recursive — provenance of the provenance), and transformation history.
           What every "citation," "attribution," "chain of custody," "audit trail,"
           "source attribution," and "metadata" actually is, when applied to knowledge.
           — Provenance is the epistemic equivalent of double-entry bookkeeping:
             it makes the knowledge economy auditable.
           — Source: SRC-K001, SRC-K004, SRC-K007, SRC-K011
           — CROSS-SUBSTRATE NOTE: Computational provenance (the chain of how data was
             processed) is maintained by SUBSTRATE-COMPUTE (TERM-C018). Epistemic
             provenance (the chain of how a claim was derived from evidence) is maintained
             here. Together they answer both "how was this computed?" and "why do we
             believe this?" See CROSS-SUBSTRATE-CONVENTIONS.md §7 Primitive Ownership Table.

TERM-K005: Context = The set of conditions, assumptions, and scope limitations under
           which a Proposition holds. Has: domain, temporal scope (valid from/until),
           spatial scope (jurisdiction, region, environment), assumption set (list of
           Propositions treated as given), and precision scope (significant figures,
           margin of error).
           What every "scope," "caveat," "precondition," "assumption," "frame of
           reference," "boundary condition," and "applicable domain" actually is.
           — A Proposition without Context is underspecified. "Water boils at 100°C"
             requires Context: {pressure: 1 atm, purity: distilled, altitude: sea level}.
           — Source: SRC-K001, SRC-K002, SRC-K003, SRC-K008
```

### Reasoning Primitives (the mechanics of thought)

```
TERM-K006: Inference = A single reasoning step that derives a new Proposition (or modifies
           Confidence in an existing one) from one or more input Propositions and/or
           Evidence, using a specified Method. Has: inputs (Propositions + Evidence),
           output (Proposition or Confidence update), Method, strength, and validity
           conditions.
           What every "deduction," "induction," "abduction," "logical step," "derivation
           step," "reasoning," and "conclusion" actually is.
           — An Inference is NOT a black box. Its Method must be inspectable.
           — An Inference chain is an Argument (TERM-K015).
           — Source: SRC-K004, SRC-K008, SRC-K012

TERM-K007: Method = A named, versioned, inspectable procedure for generating Inferences
           or evaluating Evidence. Has: name, formal description, assumptions, known
           limitations, applicable domains, and validity conditions.
           Types: deductive (formal logic), inductive (statistical), abductive
           (inference to best explanation), analogical (cross-domain mapping), Bayesian
           (probability update), meta-analytic (synthesis across studies), causal
           (interventionist/counterfactual).
           What every "methodology," "analytical technique," "statistical test,"
           "reasoning framework," and "inference rule" actually is.
           — Methods are first-class objects, not implicit. "I used Bayesian updating"
             is not sufficient — the specific prior, likelihood function, and
             computational procedure must be recorded.
           — Source: SRC-K004, SRC-K008, SRC-K012

TERM-K008: Dependency = A directed, typed link indicating that one Proposition's truth
           or Confidence depends on another Proposition. Has: source Proposition, target
           Proposition, type (logical_entailment, evidential_support, assumption,
           definitional, causal), and strength.
           What every "depends on," "follows from," "assumes," "requires," and
           "is contingent upon" actually is.
           — Dependencies form a directed acyclic graph (the Dependency Graph). Cycles
             are Contradictions (circular reasoning) and must be surfaced.
           — Source: SRC-K001, SRC-K008, SRC-K012

TERM-K009: Contradiction = A detected state where two or more Propositions in the same
           Context cannot all hold simultaneously. Has: conflicting Propositions,
           detection method, severity (logical_impossibility, empirical_tension,
           statistical_inconsistency), and resolution status (unresolved, resolved,
           acknowledged_disagreement).
           What every "conflict," "inconsistency," "paradox," "discrepancy,"
           and "anomaly" actually is.
           — NOTE: "Disagreement" between agents is a COMMUNICATION phenomenon (agents
             asserting conflicting Propositions via Speech Acts). Contradiction is the
             underlying logical state that a disagreement may reveal. See SUBSTRATE-
             COMMUNICATION TERM-M008 (Objection) and CROSS-SUBSTRATE-CONVENTIONS.md §6 P1.
           — Contradictions are NEVER silently resolved. They persist as first-class
             objects until explicitly addressed by an Actor.
           — Source: SRC-K001, SRC-K003, SRC-K004, SRC-K005

TERM-K010: Revision = An immutable record that a Proposition's Confidence changed.
           Has: proposition, old_confidence, new_confidence, trigger (Evidence,
           Inference, retraction, correction), actor, timestamp, and rationale.
           What every "update," "correction," "retraction," "amendment," and
           "belief change" actually is.
           — Revisions are the Events of the knowledge event log. The history of
             belief change IS itself knowledge.
           — Source: SRC-K001, SRC-K008, SRC-K012
```

### Structural Primitives (the architecture of meaning)

```
TERM-K011: Concept = A named, defined unit of meaning within an Ontology. Has: name,
           definition (itself a Proposition), synonyms, translations, parent concepts,
           child concepts, and cross-domain mappings.
           What every "term," "category," "class," "type," "tag," "keyword," "topic,"
           and "subject heading" actually is.
           — Concepts are the nodes of ontologies. They give Propositions their
             vocabulary.
           — Source: SRC-K002, SRC-K006

TERM-K012: Relation = A typed, directed, defined connection between two Concepts.
           Types: taxonomic (is_a, part_of, instance_of), mereological (has_part,
           contains), causal (causes, prevents, enables), temporal (precedes, follows,
           co-occurs), similarity (similar_to, analogous_to), oppositional (contradicts,
           incompatible_with).
           What every "relationship type," "semantic link," "predicate," and
           "association type" actually is.
           — Source: SRC-K006, SRC-K012

TERM-K013: Ontology = A versioned, internally consistent set of Concepts and Relations
           that defines the vocabulary of a Domain. Has: name, domain scope, version,
           concept set, relation set, axioms (constraints on valid combinations), and
           alignment mappings to other Ontologies.
           What every "taxonomy," "thesaurus," "vocabulary," "schema," "classification
           system," "terminology," and "conceptual model" actually is.
           — Multiple Ontologies may describe the same domain (competing
             classifications). This is not a defect — it is tracked as an explicit
             Ontology Alignment with gaps.
           — Source: SRC-K006

TERM-K014: Domain = A named scope of knowledge with associated Ontologies, Methods,
           quality standards, and community norms. Has: name, description, parent
           domains, child domains, ontologies, accepted methods, and quality thresholds.
           What every "field," "discipline," "subject area," "specialty," and
           "knowledge domain" actually is.
           — Domains may overlap. A Proposition may belong to multiple Domains.
             Cross-domain Propositions are the most valuable and the least well-served
             by existing systems.
           — Source: SRC-K001, SRC-K006
```

### Inquiry Primitives (the scientific method, formalized)

```
TERM-K015: Argument = A structured, inspectable chain of Inferences from Evidence and
           Propositions to a Conclusion (itself a Proposition). Has: premises (list of
           Propositions + Evidence), inference chain (ordered list of Inferences),
           conclusion (Proposition), strength, and known weaknesses.
           What every "proof," "case," "analysis," "reasoning chain," "justification,"
           and "rationale" actually is.
           — An Argument is the highest-level reasoning artifact. It is to knowledge
             what a Transaction is to commerce: a complete, auditable unit.
           — Source: SRC-K004, SRC-K008, SRC-K012

TERM-K016: Question = A formally stated gap in knowledge that the system can reason about.
           Has: content (what is being asked), presuppositions (Propositions assumed true
           for the purpose of the question), answer space (constraints on valid answers),
           priority, and status (open, answered, dissolved, superseded).
           What every "research question," "hypothesis to test," "query," "issue,"
           "problem," and "open question" actually is.
           — A Question is not a search query. It's a first-class epistemic object
             that persists, collects Evidence, and tracks progress toward resolution.
           — Source: SRC-K001, SRC-K004

TERM-K017: Hypothesis = A candidate answer to a Question, with associated Evidence,
           Arguments, and Confidence. Has: question (ref), claim (Proposition),
           supporting arguments, competing hypotheses, and discriminating evidence
           (evidence that would distinguish this Hypothesis from alternatives).
           What every "theory," "conjecture," "proposed explanation," "candidate
           diagnosis," and "working assumption" actually is.
           — Hypotheses exist in sets. A Hypothesis is meaningless without its
             alternatives. The system always tracks the full hypothesis space for a
             Question.
           — Source: SRC-K001, SRC-K004, SRC-K009

TERM-K018: Experiment = A planned procedure designed to generate Evidence that
           discriminates between Hypotheses. Has: question (ref), hypotheses under test,
           protocol (Method), predicted outcomes per hypothesis, required resources,
           status (designed, approved, in_progress, completed, abandoned), and results
           (Evidence, once completed).
           What every "study," "trial," "test," "investigation," "assessment," and
           "evaluation protocol" actually is.
           — An Experiment is valuable BEFORE its results exist. The design itself
             is knowledge (it specifies what Evidence would change what beliefs).
           — Source: SRC-K001, SRC-K004, SRC-K011

TERM-K019: Observation = Raw, minimally interpreted data from the world. Has: content
           (measurement, reading, recording, image, signal), instrument/sensor (Source),
           collection conditions (Context), precision, and timestamp.
           What every "data point," "measurement," "reading," "record," and "raw data"
           actually is.
           — Observations become Evidence when they are interpreted in the context of
             a Proposition. The same Observation can be Evidence for multiple
             Propositions. Observations are immutable; interpretations are Inferences.
           — Source: SRC-K001, SRC-K011
```

### Agent and Governance Primitives

```
TERM-K020: Source = An origin of Evidence, Observations, or Propositions. Types: human
           agent, AI agent, instrument/sensor, publication, database, institution.
           Has: identity, type, reliability history (calibration), known biases,
           domain expertise, and trust level.
           What every "author," "publisher," "journal," "sensor," "database,"
           "informant," and "reference source" actually is.
           — Sources have Calibration histories. A Source that has been reliable in
             Domain X is not necessarily reliable in Domain Y.
           — Source: SRC-K001, SRC-K004, SRC-K007

TERM-K021: Calibration = A meta-assessment of a Source's or Method's reliability,
           measured by comparing its past claims/predictions against outcomes.
           Has: subject (Source or Method), domain, metric (Brier score, accuracy,
           precision/recall, calibration curve), measurement period, and trend.
           What every "source reliability," "track record," "quality score," "impact
           factor," "h-index," and "credibility assessment" actually is — but done
           rigorously rather than as vanity metrics.
           — Source: SRC-K001, SRC-K004, SRC-K012

TERM-K022: Epistemic Envelope = The bounded authority within which an AI Agent operates
           on knowledge. Specifies: accessible Domains, permitted operations (read,
           propose, infer, revise), confidence-change thresholds requiring human
           approval, maximum inference chain depth, and prohibited conclusion types.
           — Extends SUBSTRATE's Agent Envelope concept to the epistemic domain.
           — Source: ASM-K006
           — CROSS-SUBSTRATE ENVELOPE ARCHITECTURE: An AI Agent's total authority is
             governed by domain-specific Envelopes in each substrate it operates within:
             • SUBSTRATE (Business): Agent Envelope (TERM-030) — entity scope, workflow scope, spend limits
             • SUBSTRATE-KNOWLEDGE: Epistemic Envelope (TERM-K022) — proposition scope, confidence thresholds
             • SUBSTRATE-COMPUTE: Compute Envelope (TERM-C019) — resource limits, duration limits
             • SUBSTRATE-COMMUNICATION: Communicative Envelope (TERM-M013) — discourse scope, speech act types, commitment limits
             SUBSTRATE (Business) is the authoritative source for agent identity and
             principal assignment. An agent MUST have a Business Agent Envelope to exist.
             Domain-specific envelopes extend (never exceed) the base authority. If no
             domain-specific envelope exists for an agent in a given substrate, the agent
             has zero authority in that domain (deny by default). The agent's effective
             authority in any operation is the most restrictive applicable envelope.
             See CROSS-SUBSTRATE-CONVENTIONS.md §1, §6 Principle P3.

TERM-K023: Consensus = A multi-agent agreement (or documented disagreement) on a
           Proposition's status. Has: proposition, participating actors, agreement
           level (unanimous, majority, supermajority, contested), dissenting positions,
           method of consensus (vote, Delphi, structured debate, formal proof
           verification), and timestamp.
           — Consensus is recorded, not enforced. A minority position is not deleted
             — it persists with its Arguments accessible.
           — Source: SRC-K001, SRC-K004, SRC-K012
           — CROSS-SUBSTRATE NOTE: Consensus *formation* (the discourse process of voting,
             debating, deliberating) is a COMMUNICATION capability (TERM-M018). Consensus
             *recording* (the epistemic fact that agreement was reached) is a KNOWLEDGE
             capability. When consensus is reached via discourse, KNOWLEDGE references
             the COMMUNICATION Consensus Record for process details.
             See CROSS-SUBSTRATE-CONVENTIONS.md §6 Principle P1.
```

### Interface Primitives

```
TERM-K024: Query = A structured request for knowledge retrieval, inference, or
           computation. Has: content (what is sought), scope (Domains, time range,
           Sources), depth (surface retrieval vs. deep inference), and response
           format (Propositions, Arguments, Evidence, or summary).
           What every "search," "lookup," "question," "request for information,"
           and "research query" actually is.
           — A Query against SUBSTRATE-KNOWLEDGE returns not just answers but
             provenance, confidence, and competing alternatives.
           — Source: SRC-K001, SRC-K005

TERM-K025: View = A saved query + layout declaration that presents knowledge artifacts
           to an Actor. Types: knowledge graph visualization, evidence table,
           confidence timeline, dependency map, contradiction report, hypothesis
           comparison matrix, provenance chain, domain overview.
           What every "dashboard," "report," "visualization," "knowledge map," and
           "literature review" actually is.
           — Views are read-only projections. They never mutate knowledge state.
           — Source: SRC-K005, SRC-K009

TERM-K026: Annotation = A commentary, note, or qualifier attached to any knowledge
           artifact (Proposition, Evidence, Argument, etc.) by an Actor. Has: target
           (ref to any knowledge artifact), content, author, timestamp, and type
           (comment, correction, question, endorsement, challenge, caveat).
           What every "note," "comment," "footnote," "margin note," "peer review
           comment," and "editorial note" actually is.
           — Annotations are themselves Propositions (about other Propositions).
             They participate in provenance and revision tracking.
           — Source: SRC-K001, SRC-K005, SRC-K007
           — CROSS-SUBSTRATE NOTE: The *act* of creating an Annotation (e.g., during
             peer review) may involve COMMUNICATION discourse. The Annotation *content*
             — the epistemic commentary — is a KNOWLEDGE Proposition. COMMUNICATION
             tracks the dialogue; KNOWLEDGE records the result.
             See CROSS-SUBSTRATE-CONVENTIONS.md §6 Principle P1.
```

---

## 4. CORE CAPABILITIES (WHAT IT CAN DO)

### Proposition Management

```
CAP-K001 (MUST):     The system MUST allow any authenticated Actor to create Propositions
                     with associated Context, initial Confidence, and Provenance.
                     — Source: SRC-K001 through SRC-K012

CAP-K002 (MUST):     The system MUST enforce that every Proposition has non-empty Provenance
                     at creation. Anonymous claims are forbidden.
                     — Source: ASM-K004

CAP-K003 (MUST):     The system MUST record an immutable Revision event for every Confidence
                     change on every Proposition, including the trigger, actor, and rationale.
                     — Source: ASM-K002, ASM-K008

CAP-K004 (MUST NOT): The system MUST NOT permanently delete any Proposition. Deprecated
                     Propositions are marked as superseded/retracted with a reference to the
                     superseding Proposition and rationale. Historical states remain queryable.
                     — Source: ASM-K001, ASM-K008

CAP-K005 (MUST):     The system MUST allow any Actor with read permission to query the
                     Confidence of any Proposition at any past point in time (belief
                     time-travel).
                     — Source: ASM-K008

CAP-K006 (MUST):     The system MUST automatically detect and surface Contradictions when
                     a new Proposition or Confidence change creates a logical or evidential
                     conflict with existing Propositions in the same Context.
                     — Source: ASM-K005
```

### Evidence and Provenance

```
CAP-K007 (MUST):     The system MUST maintain complete Provenance chains: every Proposition
                     must trace through its Evidence, Sources, and Inference Methods to its
                     ultimate origins.
                     — Source: ASM-K004

CAP-K008 (MUST):     The system MUST allow Evidence to be linked to multiple Propositions
                     with independent support/undermine assessments per link.
                     — Source: SRC-K001

CAP-K009 (MUST NOT): The system MUST NOT allow modification of recorded Evidence. New
                     interpretations of existing Evidence are new Inferences, not edits.
                     — Source: ASM-K008

CAP-K010 (MUST):     The system MUST accept Evidence from External Systems (ACT-K006) with
                     mandatory Source identification and automatic confidence floor
                     application for unverified Sources.
                     — Source: SRC-K006
```

### Inference and Reasoning

```
CAP-K011 (MUST):     The system MUST evaluate Inferences using the specified Method and
                     record the complete inference chain (inputs, method, output) as an
                     auditable artifact.
                     — Source: ASM-K009, NG-K002

CAP-K012 (MUST):     The system MUST propagate Confidence changes through the Dependency
                     Graph: when a Proposition's Confidence changes, all Propositions that
                     depend on it must have their Confidence re-evaluated.
                     — Source: SRC-K008, UNK-K002

CAP-K013 (MUST):     The system MUST detect cycles in the Dependency Graph and surface
                     them as circular-reasoning Contradictions.
                     — Source: SRC-K008, SRC-K012

CAP-K014 (MUST NOT): The system MUST NOT perform opaque inference. Every Confidence value
                     must be decomposable into its contributing Evidence, Inferences, and
                     Methods.
                     — Source: NG-K002

CAP-K015 (SHOULD):   The system SHOULD suggest relevant Hypotheses and counter-Evidence
                     when an Actor is evaluating a Proposition, to mitigate confirmation bias.
                     — Source: SRC-K004, SRC-K013
```

### Ontology and Structure

```
CAP-K016 (MUST):     The system MUST allow ACT-K003 to define, version, and publish
                     Ontologies with Concepts, Relations, and axioms.
                     — Source: SRC-K006

CAP-K017 (MUST):     The system MUST support multiple co-existing Ontologies for the
                     same Domain, with explicit Alignment mappings (concept equivalence,
                     subsumption, overlap) between them.
                     — Source: SRC-K006, UNK-K003

CAP-K018 (MUST):     The system MUST allow cross-Domain reasoning: Propositions, Evidence,
                     and Inferences may reference Concepts from multiple Ontologies.
                     — Source: ASM-K012
```

### Scientific Method Support

```
CAP-K019 (MUST):     The system MUST support the full Question → Hypothesis → Experiment →
                     Observation → Evidence → Inference → Proposition lifecycle as
                     first-class workflow.
                     — Source: SRC-K001, SRC-K011

CAP-K020 (MUST):     The system MUST track all Hypotheses for a given Question as a set,
                     including those rejected, with their rejection Evidence and reasoning.
                     — Source: SRC-K004

CAP-K021 (MUST):     The system MUST link Experiment designs to their predicted outcomes
                     per Hypothesis, enabling discrimination analysis (which experiment
                     would most efficiently distinguish between competing hypotheses).
                     — Source: SRC-K004, SRC-K011
```

### Access, Agents & Security

```
CAP-K022 (MUST NOT): The system MUST NOT allow any AI Agent to perform any epistemic
                     operation outside its Epistemic Envelope. Envelope enforcement occurs
                     at the permission layer.
                     — Source: ASM-K006

CAP-K023 (MUST):     The system MUST mark all machine-generated Propositions with
                     immutable `authored_by_ai: true` metadata that cannot be overridden
                     by any Actor including system administrators.
                     — Source: ASM-K006, UNK-K005

CAP-K024 (MUST):     The system MUST allow any Actor to export ALL knowledge artifacts
                     in their scope in open, machine-readable formats at any time.
                     — Source: NG-K003

CAP-K025 (MUST NOT): The system MUST NOT allow cross-Organization knowledge access without
                     explicit, revocable, audited permission grants.
                     — Source: NG-K003

CAP-K026 (MUST):     The system MUST operate in offline/local mode for all read operations
                     and queue write operations for synchronization when connectivity is
                     restored.
                     — Source: ASM-K007

CAP-K027 (MUST):     The system MUST provide Calibration tracking for all Sources and Methods,
                     enabling Actors to assess reliability history before trusting a claim.
                     — Source: SRC-K004, SRC-K012
```

---

## 5. DOMAIN OBJECTS & STATE

### 5.1 Core Knowledge Objects

```
ENT-K001: Proposition — Source: SRC-K001 through SRC-K012
  Purpose:        The atomic unit of knowledge. Everything the system tracks.
  Attributes:
    - content           | text       | structured claim, ≤4KB      | required
    - formal_content    | expression | machine-readable form       | optional
    - context           | ref ENT-K005 (Context)                   | required
    - confidence        | ref ENT-K003 (Confidence)                | required
    - provenance        | ref ENT-K004 (Provenance)                | required
    - domain            | ref ENT-K014 (Domain)                    | required  | ≥1
    - dependencies      | list<ref ENT-K008 (Dependency)>          | optional
    - evidence_links    | list<ref ENT-K002>                       | optional
    - tags              | list<ref ENT-K011 (Concept)>             | optional
    - status            | enum                                     | required
    - authored_by_ai    | boolean                                  | required  | immutable
    - version           | integer                                  | auto-increment
  Identity:       UUID + Organization scope + version
  Lifecycle:      Draft → Published → Challenged → Revised → Superseded → Retracted
  Persistence:    Event-sourced. Current confidence = materialized view of Revision log.
  Constraints:    Provenance MUST be non-empty. Context MUST be non-empty.
                  authored_by_ai is set at creation and CANNOT be modified.
  Derived state:  current_confidence = latest Confidence assessment
                  contradiction_count = COUNT(active Contradictions involving this Proposition)
                  evidence_count = COUNT(linked Evidence)
                  dependency_depth = MAX(path length to any root in Dependency Graph)

ENT-K002: Evidence — Source: SRC-K001 through SRC-K012
  Purpose:        An artifact bearing on the truth of Propositions.
  Attributes:
    - content           | text or blob-ref  | ≤10MB inline, else ref | required
    - content_type      | MIME type                                   | required
    - source            | ref ENT-K020 (Source)                       | required
    - collection_method | ref ENT-K007 (Method)                       | optional
    - collection_context| ref ENT-K005 (Context)                      | required
    - quality_grade     | enum(high, moderate, low, unassessed)       | required
    - timestamp         | datetime with uncertainty                    | required
    - proposition_links | list<{proposition: ref, direction: supports|undermines, strength: strong|moderate|weak}>
    - version           | integer                                     | auto-increment
  Identity:       UUID + Organization scope
  Lifecycle:      Submitted → Verified → Active → Deprecated
  Persistence:    Immutable once Active. New interpretations are new Inferences.
  Constraints:    Source MUST be identified. collection_context MUST be non-empty.
                  Content MUST NOT be modified after status = Active.

ENT-K003: Confidence — Source: SRC-K003, SRC-K004, SRC-K008
  Purpose:        A calibrated belief assessment attached to a Proposition.
  Attributes:
    - value             | decimal [0, 1]                               | required
    - lower_bound       | decimal [0, 1]                               | required
    - upper_bound       | decimal [0, 1]                               | required
    - method            | ref ENT-K007 (Method)                        | required
    - assessor          | ref Actor                                    | required
    - contributing_evidence | list<ref ENT-K002>                       | required  | ≥0
    - contributing_inferences | list<ref ENT-K006>                     | optional
    - timestamp         | datetime                                     | required
  Identity:       UUID (part of Proposition's revision history)
  Lifecycle:      N/A — immutable once created. New assessments are new instances.
  Constraints:    lower_bound ≤ value ≤ upper_bound.
                  value = 1.0 requires method = "axiomatic" or "formal_proof".
                  Assessor type (human vs AI) recorded immutably.

ENT-K004: Provenance — Source: ASM-K004, SRC-K001, SRC-K007
  Purpose:        Chain of origin and custody for any knowledge artifact.
  Attributes:
    - target            | ref (any knowledge artifact)                 | required
    - creator           | ref Actor                                    | required
    - creation_timestamp| datetime                                     | required
    - method            | ref ENT-K007 (Method)                        | optional
    - source_chain      | list<ref ENT-K004>                           | optional  | recursive
    - derivation_inputs | list<ref (Proposition | Evidence | Observation)> | optional
    - transformation    | text (description of what was done)          | optional
  Identity:       UUID
  Lifecycle:      Immutable once created.
  Constraints:    creator MUST be identified. Cycles in source_chain are forbidden.

ENT-K005: Context — Source: SRC-K001, SRC-K002, SRC-K003
  Purpose:        The scope and conditions under which a Proposition holds.
  Attributes:
    - domain_scope      | list<ref ENT-K014 (Domain)>                  | optional
    - temporal_scope    | { valid_from: datetime, valid_until: datetime | null }  | optional
    - spatial_scope     | { jurisdictions, regions, environments }      | optional
    - assumptions       | list<ref ENT-K001 (Proposition)>             | optional
    - precision         | { significant_figures, margin_of_error }     | optional
    - conditions        | text (human-readable statement of conditions)| optional
  Identity:       UUID + Organization scope
  Lifecycle:      Created → Active → Archived
  Constraints:    At least one scope dimension MUST be specified.
```

### 5.2 Reasoning Objects

```
ENT-K006: Inference — Source: SRC-K004, SRC-K008, SRC-K012
  Purpose:        A single auditable reasoning step.
  Attributes:
    - inputs            | list<ref (Proposition | Evidence)>           | required  | ≥1
    - output            | ref (Proposition — new or Confidence update) | required
    - method            | ref ENT-K007 (Method)                        | required
    - strength          | enum(conclusive, strong, moderate, weak, suggestive) | required
    - validity_conditions | list<ref ENT-K005 (Context)>               | optional
    - authored_by_ai    | boolean                                      | required  | immutable
    - rationale         | text                                         | required
  Identity:       UUID
  Lifecycle:      Proposed → Accepted → Challenged → Withdrawn
  Constraints:    Method MUST be inspectable. Inputs must all be accessible to the Actor.

ENT-K007: Method — Source: SRC-K004, SRC-K008, SRC-K012
  Purpose:        A named, inspectable reasoning or evidence-generation procedure.
  Attributes:
    - name              | text                                         | required
    - type              | enum(deductive, inductive, abductive, bayesian,
                          statistical, meta_analytic, causal, analogical,
                          heuristic, formal_verification, experimental)  | required
    - description       | text                                         | required
    - formal_spec       | text (formal description, if available)      | optional
    - assumptions       | list<text>                                   | required
    - known_limitations | list<text>                                   | required
    - applicable_domains| list<ref ENT-K014>                           | optional
    - calibration       | ref ENT-K021 (latest Calibration)            | optional
    - version           | integer                                      | auto-increment
  Identity:       UUID + version
  Lifecycle:      Draft → Published → Deprecated
  Constraints:    known_limitations MUST be non-empty (every Method has limitations).

ENT-K008: Dependency — Source: SRC-K001, SRC-K008
  Purpose:        A directed link showing epistemic dependence between Propositions.
  Attributes:
    - source            | ref ENT-K001 (the Proposition that depends)  | required
    - target            | ref ENT-K001 (the Proposition depended upon) | required
    - type              | enum(logical_entailment, evidential_support,
                          assumption, definitional, causal, analogical) | required
    - strength          | enum(necessary, strong, moderate, weak)      | required
    - inference         | ref ENT-K006 (the Inference that established this) | optional
  Identity:       UUID
  Lifecycle:      Active → Dissolved (when reasoning invalidated)
  Constraints:    Global Dependency Graph MUST be acyclic. Cycle detection on every
                  write. Cycles surfaced as Contradictions (circular reasoning).

ENT-K009: Contradiction — Source: ASM-K005, SRC-K001, SRC-K003
  Purpose:        A surfaced conflict between Propositions.
  Attributes:
    - propositions      | list<ref ENT-K001>                           | required  | ≥2
    - type              | enum(logical_impossibility, empirical_tension,
                          statistical_inconsistency, definitional_conflict,
                          circular_reasoning)                           | required
    - severity          | enum(hard — cannot coexist, soft — tension)  | required
    - context           | ref ENT-K005                                 | required
    - detection_method  | enum(automatic, manual, agent_reported)      | required
    - resolution_status | enum(unresolved, resolved, acknowledged_disagreement,
                          dissolved — context changed)                  | required
    - resolution        | { method: text, actor: ref, timestamp: datetime,
                          chosen_proposition: ref | null }             | optional
  Identity:       UUID
  Lifecycle:      Detected → Under_Review → Resolved | Acknowledged | Dissolved
  Constraints:    MUST persist until explicitly resolved. MUST NOT be auto-resolved
                  by the system without Actor intervention (except for dissolution
                  when Context invalidates the conflict).

ENT-K010: Revision — Source: ASM-K002, ASM-K008
  Purpose:        An immutable record of knowledge state change.
  Attributes:
    - target            | ref (any knowledge artifact)                 | required
    - change_type       | enum(confidence_update, status_change, context_change,
                          evidence_added, evidence_removed, retraction,
                          correction, supersession, merge)              | required
    - old_state         | snapshot of changed fields                   | required
    - new_state         | snapshot of changed fields                   | required
    - trigger           | ref (Evidence | Inference | Contradiction | Actor action) | required
    - actor             | ref Actor                                    | required
    - rationale         | text                                         | required
    - timestamp         | datetime                                     | required
  Identity:       UUID + sequence number per target artifact
  Lifecycle:      Immutable. Created once, never modified.
  Constraints:    Hash-chained per target artifact (each Revision includes hash of
                  previous Revision for the same target). rationale MUST be non-empty.
```

### 5.3 Structural Objects

```
ENT-K011: Concept — Source: SRC-K006
  Purpose:        A unit of meaning in an Ontology.
  Attributes:
    - name              | text                                         | required
    - definition        | text (or ref ENT-K001 — definition as Proposition) | required
    - synonyms          | list<text>                                   | optional
    - translations      | map<language_code, text>                     | optional
    - ontology          | ref ENT-K013                                 | required
    - parent_concepts   | list<ref ENT-K011>                           | optional
    - child_concepts    | list<ref ENT-K011>                           | optional  | derived
    - cross_mappings    | list<{ target: ref ENT-K011, alignment: exact|broader|
                          narrower|related, confidence: decimal }>     | optional
  Identity:       UUID + Ontology scope
  Lifecycle:      Draft → Published → Deprecated
  Constraints:    Name unique within Ontology. Taxonomic hierarchy MUST be acyclic.

ENT-K012: Relation — Source: SRC-K006, SRC-K012
  Purpose:        A typed link between Concepts.
  Attributes:
    - source            | ref ENT-K011                                 | required
    - target            | ref ENT-K011                                 | required
    - type              | enum(is_a, part_of, has_part, instance_of, causes,
                          prevents, enables, precedes, follows, co_occurs,
                          similar_to, analogous_to, contradicts, incompatible_with,
                          derived_from, component_of, regulates, inhibits,
                          specializes, generalizes)                     | required
    - direction         | enum(directed, symmetric)                    | required
    - properties        | map<text, text>                              | optional
  Identity:       UUID
  Lifecycle:      Active → Deprecated
  Constraints:    is_a hierarchy MUST be acyclic within an Ontology.

ENT-K013: Ontology — Source: SRC-K006
  Purpose:        A structured vocabulary for a Domain.
  Attributes:
    - name              | text                                         | required
    - description       | text                                         | required
    - domain            | ref ENT-K014                                 | required
    - concepts          | list<ref ENT-K011>                           | required  | ≥1
    - relations         | list<ref ENT-K012>                           | optional
    - axioms            | list<Expression>                             | optional
    - alignments        | list<{ target_ontology: ref ENT-K013,
                          mappings: list<ref ENT-K011.cross_mappings> }> | optional
    - version           | integer                                      | auto-increment
  Identity:       UUID + Organization scope + version
  Lifecycle:      Draft → Published → Deprecated
  Constraints:    Concepts must have unique names within Ontology. Axioms must be
                  satisfiable (checked at publish time).

ENT-K014: Domain — Source: SRC-K001, SRC-K006
  Purpose:        A named scope of knowledge.
  Attributes:
    - name              | text                                         | required
    - description       | text                                         | required
    - parent_domains    | list<ref ENT-K014>                           | optional
    - child_domains     | list<ref ENT-K014>                           | optional  | derived
    - ontologies        | list<ref ENT-K013>                           | optional  | derived
    - accepted_methods  | list<ref ENT-K007>                           | optional
    - quality_thresholds| { min_evidence_grade, min_method_type,
                          confidence_threshold_for_publication }       | optional
  Identity:       UUID + Organization scope
  Lifecycle:      Active → Archived
  Constraints:    Domain hierarchy MUST be acyclic.
```

### 5.4 Inquiry Objects

```
ENT-K015: Argument — Source: SRC-K004, SRC-K008, SRC-K012
  Purpose:        A complete, auditable reasoning chain.
  Attributes:
    - name              | text                                         | required
    - premises          | list<ref (ENT-K001 | ENT-K002)>             | required  | ≥1
    - inference_chain   | list<ref ENT-K006>                           | required  | ≥1
    - conclusion        | ref ENT-K001                                 | required
    - strength          | enum(deductive_valid, inductively_strong,
                          abductively_plausible, weak, fallacious)     | required
    - known_weaknesses  | list<text>                                   | required
    - counter_arguments | list<ref ENT-K015>                           | optional
                          CROSS-SUBSTRATE NOTE: Counter-arguments are Knowledge artifacts —
                          other reasoning chains that reach opposing conclusions. The *act*
                          of challenging an Argument in discourse is a COMMUNICATION operation
                          (Objection Speech Act, TERM-M008). Counter-arguments may be
                          discovered through discourse, imported from literature, or generated
                          by AI agents. See CROSS-SUBSTRATE-CONVENTIONS.md §6 Principle P1.
    - authored_by_ai    | boolean                                      | required
    - version           | integer                                      | auto-increment
  Identity:       UUID
  Lifecycle:      Proposed → Under_Review → Accepted → Withdrawn
                  NOTE: The previous "Challenged" state has been removed. Challenges to
                  Arguments are conducted via SUBSTRATE-COMMUNICATION discourse (Objection
                  Speech Acts). An Argument with active counter-arguments is not in a special
                  state — it simply has counter-arguments. The Under_Review state may be
                  re-entered from Accepted when a cross-substrate event from COMMUNICATION
                  indicates a formal challenge Discourse has been opened.
  Constraints:    inference_chain must form a valid path from premises to conclusion.
                  known_weaknesses MUST be non-empty (no Argument is without weakness).

ENT-K016: Question — Source: SRC-K001, SRC-K004
  Purpose:        A formally stated gap in knowledge.
  Attributes:
    - content           | text                                         | required
    - presuppositions   | list<ref ENT-K001>                           | optional
    - answer_constraints| { type: enum(proposition, value, entity_ref, set),
                          domain: ref ENT-K014, format: text }         | optional
    - priority          | enum(critical, high, medium, low)            | required
    - status            | enum(open, partially_answered, answered,
                          dissolved, superseded)                        | required
    - hypotheses        | list<ref ENT-K017>                           | optional  | derived
    - assigned_to       | list<ref Actor>                              | optional
    - deadline          | datetime                                     | optional
    - parent_question   | ref ENT-K016                                 | optional
    - sub_questions     | list<ref ENT-K016>                           | optional  | derived
  Identity:       UUID + Organization scope
  Lifecycle:      Open → In_Progress → Answered → Closed | Dissolved | Superseded
  Constraints:    Answered requires at least one Hypothesis with confidence above
                  Domain's quality_threshold. Dissolved requires rationale.

ENT-K017: Hypothesis — Source: SRC-K001, SRC-K004, SRC-K009
  Purpose:        A candidate answer to a Question.
  Attributes:
    - question          | ref ENT-K016                                 | required
    - claim             | ref ENT-K001 (the proposed Proposition)      | required
    - prior_confidence  | ref ENT-K003                                 | required
    - current_confidence| ref ENT-K003                                 | required  | derived
    - supporting_arguments | list<ref ENT-K015>                        | optional
    - competing_with    | list<ref ENT-K017>                           | optional  | derived
    - discriminating_evidence | list<{ evidence: ref ENT-K002,
                                 predicted_if_true: text,
                                 predicted_if_false: text }>           | optional
    - status            | enum(proposed, under_investigation, supported,
                          weakened, rejected, confirmed)                | required
  Identity:       UUID
  Lifecycle:      Proposed → Under_Investigation → Supported | Rejected
  Constraints:    Must reference an open Question. competing_with auto-derived from
                  other Hypotheses on the same Question.

ENT-K018: Experiment — Source: SRC-K001, SRC-K004, SRC-K011
  Purpose:        A planned procedure to generate discriminating Evidence.
  Attributes:
    - name              | text                                         | required
    - question          | ref ENT-K016                                 | required
    - hypotheses_tested | list<ref ENT-K017>                           | required  | ≥2
    - protocol          | ref ENT-K007 (Method)                        | required
    - predicted_outcomes| list<{ hypothesis: ref ENT-K017,
                           predicted: text, confidence_if_observed: decimal }> | required
    - required_resources| text                                         | optional
    - status            | enum(designed, approved, in_progress,
                          completed, abandoned)                         | required
    - results           | list<ref ENT-K002 (Evidence)>                | optional
    - pre_registration  | { registered_at: datetime, registry: text,
                          hash: text }                                 | optional
  Identity:       UUID
  Lifecycle:      Designed → Approved → In_Progress → Completed | Abandoned
  Constraints:    Must test ≥2 Hypotheses (otherwise it's not discriminating).
                  predicted_outcomes must cover each Hypothesis tested.

ENT-K019: Observation — Source: SRC-K001, SRC-K011
  Purpose:        Raw data from the world, prior to interpretation.
  Attributes:
    - content           | text or blob-ref                             | required
    - content_type      | MIME type                                    | required
    - instrument        | ref ENT-K020 (Source — instrument type)      | optional
    - collection_context| ref ENT-K005                                 | required
    - precision         | { value: decimal, unit: text }               | optional
    - timestamp         | datetime with uncertainty bounds              | required
    - raw               | boolean (true if unprocessed)                | required
  Identity:       UUID
  Lifecycle:      Recorded → Verified → Active → Archived
  Constraints:    Immutable once Active. Content MUST NOT be modified.
```

### 5.5 Agent and Governance Objects

```
ENT-K020: Source — Source: SRC-K001, SRC-K004, SRC-K007
  Purpose:        An origin of knowledge artifacts.
  Attributes:
    - name              | text                                         | required
    - type              | enum(human_agent, ai_agent, instrument, sensor,
                          publication, database, institution, composite) | required
    - identity          | ref Actor or external identifier             | required
    - domains_of_expertise | list<ref ENT-K014>                        | optional
    - known_biases      | list<text>                                   | optional
    - calibration_history | list<ref ENT-K021>                         | optional  | derived
    - trust_level       | enum(verified, provisional, unverified, blacklisted) | required
  Identity:       UUID + Organization scope
  Lifecycle:      Registered → Verified → Active → Suspended → Archived
  Constraints:    Blacklisted Sources' Propositions carry maximum confidence penalty.
                  trust_level changes logged as Revision events.

ENT-K021: Calibration — Source: SRC-K004, SRC-K012
  Purpose:        Reliability assessment of a Source or Method.
  Attributes:
    - subject           | ref (ENT-K020 | ENT-K007)                    | required
    - domain            | ref ENT-K014                                 | required
    - metric            | enum(brier_score, accuracy, precision, recall,
                          f1, calibration_curve, hit_rate, false_alarm_rate) | required
    - value             | decimal                                      | required
    - sample_size       | integer                                      | required
    - period            | { from: datetime, to: datetime }             | required
    - trend             | enum(improving, stable, degrading)           | required
    - details           | text or blob-ref                             | optional
  Identity:       UUID
  Lifecycle:      Computed → Published → Superseded (by newer Calibration)
  Constraints:    sample_size MUST be ≥ configured minimum (default: 20).
                  trend derived from comparison with previous Calibration.

ENT-K022: Epistemic Envelope — Source: ASM-K006
  Purpose:        Bounded authority for AI agents operating on knowledge.
  Attributes:
    - agent             | ref Actor (ACT-K004 or ACT-K005)             | required
    - domain_scope      | list<ref ENT-K014>                           | required
    - permitted_ops     | list<enum(read, propose_proposition,
                          propose_inference, update_confidence,
                          detect_contradiction, create_argument,
                          annotate, query)>                             | required
    - confidence_change_threshold | decimal (max Δ confidence without human approval) | required
    - max_inference_depth | integer                                    | required
    - prohibited_conclusion_types | list<text>                         | optional
    - rate_limit        | { operations: integer, period: duration }    | required
    - kill_switch       | boolean                                      | required  | default: false
    - human_approver    | ref Actor                                    | required
    - spend_limit       | { operations: integer, period: duration }    | required
  Identity:       UUID + Organization scope
  Lifecycle:      Created → Active → Suspended → Revoked
  Constraints:    kill_switch=true halts all operations immediately.
                  confidence_change_threshold MUST be < 0.5 for ACT-K004 (narrow agents).

ENT-K023: Consensus — Source: SRC-K001, SRC-K004
  Purpose:        Multi-agent agreement record.
  Attributes:
    - proposition       | ref ENT-K001                                 | required
    - participants      | list<ref Actor>                              | required  | ≥2
    - agreement_level   | enum(unanimous, supermajority, majority, contested,
                          deadlocked)                                   | required
    - dissenting_positions | list<{ actor: ref, position: ref ENT-K015,
                              rationale: text }>                        | optional
                          CROSS-SUBSTRATE NOTE: Dissent details (grounds, arguments, severity)
                          are maintained in SUBSTRATE-COMMUNICATION Dissent Records (TERM-M019).
                          KNOWLEDGE records the existence and identity of dissenters.
    - method            | enum(formal_proof_verification, discourse_based) | required
                          CROSS-SUBSTRATE NOTE: When method = discourse_based, the consensus
                          was reached via COMMUNICATION discourse. The specific discourse
                          method (vote, Delphi, structured debate, expert panel) is recorded
                          in COMMUNICATION's Consensus Record (ENT-M010). When method =
                          formal_proof_verification, consensus is established by formal proof
                          (no discourse needed).
    - discourse_consensus_ref | cross-substrate ref to COMMUNICATION ENT-M010 | required when method = discourse_based
    - timestamp         | datetime                                     | required
    - valid_until       | datetime | null                               | optional
  Identity:       UUID
  Lifecycle:      Initiated → In_Progress → Concluded → Expired | Superseded
  Constraints:    Dissenting positions MUST be recorded if agreement_level ≠ unanimous.
                  Minority positions are never deleted.
                  discourse_consensus_ref MUST be present when method = discourse_based.
                  See CROSS-SUBSTRATE-CONVENTIONS.md §5 for reference format.
```

---


## 5.2 State Machines

```
SM-K001: Proposition Lifecycle — Entity: ENT-K001 — Source: SRC-K001, ASM-K002
  States:      Draft, Published, Challenged, Revised, Superseded, Retracted
  Transitions:
    Draft → Published
      Trigger:       Actor submits for publication
      Preconditions: Provenance non-empty, Context non-empty, Confidence assigned,
                     at least one Domain tagged
      Postconditions: Proposition visible to all Actors with read permission.
                      Creation Event recorded.
    Published → Challenged
      Trigger:       Contradiction detected (FLOW-K003) OR Actor manually challenges
      Preconditions: At least one Contradiction linked OR challenge rationale provided
      Postconditions: Contradiction visible. Challenge Event recorded.
                      Original Proposition content unchanged.
    Challenged → Published
      Trigger:       All linked Contradictions resolved in favor of this Proposition
      Preconditions: Zero unresolved Contradictions remain
      Postconditions: Status reverted. Resolution Event recorded.
    Challenged → Revised
      Trigger:       Actor submits revised content or confidence
      Preconditions: Revision rationale provided
      Postconditions: New version created. Revision Event recorded.
                      Old version retained with full history.
    Published → Revised
      Trigger:       Actor submits updated confidence or content refinement
      Preconditions: Revision rationale provided
      Postconditions: New version. Revision Event. Old version retained.
    Revised → Published
      Trigger:       Revision accepted (by author or peer review, per Domain policy)
      Preconditions: Revised content passes all validation rules
      Postconditions: Latest version is the Published version.
    Published → Superseded
      Trigger:       New Proposition explicitly supersedes this one
      Preconditions: Superseding Proposition references this one
      Postconditions: Supersession link recorded. This Proposition still queryable.
                      Confidence queries return with "superseded" flag.
    Challenged → Retracted
      Trigger:       Author or Steward retracts
      Preconditions: Retraction rationale provided
      Postconditions: Status = Retracted. Retraction Event with rationale.
                      Proposition still queryable with "retracted" flag.
                      All dependent Propositions notified for re-evaluation.
    Published → Retracted
      Trigger:       Author or Steward retracts (e.g., error discovered, misconduct)
      Preconditions: Retraction rationale provided
      Postconditions: Same as Challenged → Retracted

SM-K002: Evidence Lifecycle — Entity: ENT-K002 — Source: SRC-K001, ASM-K008
  States:      Submitted, Verified, Active, Deprecated
  Transitions:
    Submitted → Verified
      Trigger:       Source verification complete (manual or automated)
      Preconditions: Source identified. Collection context provided.
      Postconditions: Quality grade assigned. Verification Event recorded.
    Submitted → Active
      Trigger:       Auto-accept for verified Sources (configurable per Domain)
      Preconditions: Source trust_level = verified AND Domain policy allows auto-accept
      Postconditions: Evidence available for linking to Propositions.
    Verified → Active
      Trigger:       Steward approves OR auto-approve policy applies
      Preconditions: Quality grade ≥ Domain minimum threshold
      Postconditions: Evidence linkable. Activation Event recorded.
    Active → Deprecated
      Trigger:       Newer Evidence supersedes OR methodological flaw discovered
      Preconditions: Deprecation rationale provided
      Postconditions: Evidence still queryable with "deprecated" flag.
                      Propositions relying on it notified for re-evaluation.
                      Content immutable (INV-K009 still holds).

SM-K003: Inference Lifecycle — Entity: ENT-K006 — Source: SRC-K008, SRC-K012
  States:      Proposed, Accepted, Challenged, Withdrawn
  Transitions:
    Proposed → Accepted
      Trigger:       Peer review (per Domain policy) OR auto-accept for verified Methods
      Preconditions: All inputs accessible. Method valid for Domain.
      Postconditions: Inference contributes to Confidence calculations.
                      Dependency links activated.
    Proposed → Withdrawn
      Trigger:       Author withdraws before acceptance
      Preconditions: Withdrawal rationale provided
      Postconditions: Inference no longer contributes. Withdrawal Event recorded.
    Accepted → Challenged
      Trigger:       Counter-inference proposed OR input Proposition retracted/revised
      Preconditions: Challenge rationale or triggering event identified
      Postconditions: Dependent Confidence values flagged for re-evaluation.
    Challenged → Accepted
      Trigger:       Challenge resolved in favor of this Inference
      Preconditions: Challenging evidence/argument addressed with rationale
      Postconditions: Inference restored to full contribution status.
    Challenged → Withdrawn
      Trigger:       Author or Steward withdraws after challenge
      Preconditions: Withdrawal rationale provided
      Postconditions: All dependent Confidence values re-evaluated without this Inference.
    Accepted → Withdrawn
      Trigger:       Foundational error discovered (method flaw, input invalidated)
      Preconditions: Withdrawal rationale provided
      Postconditions: Same as Challenged → Withdrawn

SM-K004: Question Lifecycle — Entity: ENT-K016 — Source: SRC-K001, SRC-K004
  States:      Open, In_Progress, Answered, Closed, Dissolved, Superseded
  Transitions:
    Open → In_Progress
      Trigger:       First Hypothesis proposed OR investigator assigned
      Preconditions: None beyond Question existence
      Postconditions: Assignment Event recorded.
    In_Progress → Answered
      Trigger:       At least one Hypothesis confidence exceeds Domain threshold
      Preconditions: Winning Hypothesis has supporting Argument with Evidence
      Postconditions: Answering Proposition linked. Answer Event recorded.
    Answered → Closed
      Trigger:       Steward or original asker confirms answer satisfactory
      Preconditions: Answer reviewed
      Postconditions: Question closed. Closure Event recorded.
    Open → Dissolved
      Trigger:       Presuppositions invalidated OR question found to be malformed
      Preconditions: Dissolution rationale provided
      Postconditions: Dissolution Event with rationale. Question still queryable.
    In_Progress → Dissolved
      Trigger:       Same as Open → Dissolved
    Open → Superseded
      Trigger:       More precise or well-formed Question replaces this one
      Preconditions: Superseding Question references this one
      Postconditions: Supersession link recorded.
    In_Progress → Superseded
      Trigger:       Same as Open → Superseded
    Answered → In_Progress
      Trigger:       New contradicting Evidence emerges OR answer confidence drops
                     below threshold
      Preconditions: Re-opening rationale provided
      Postconditions: Re-opening Event recorded. Question re-enters investigation.

SM-K005: Experiment Lifecycle — Entity: ENT-K018 — Source: SRC-K001, SRC-K011
  States:      Designed, Approved, In_Progress, Completed, Abandoned
  Transitions:
    Designed → Approved
      Trigger:       Review by domain expert or ethics board (per Domain policy)
      Preconditions: Protocol (Method) specified. ≥2 Hypotheses under test.
                     Predicted outcomes documented.
      Postconditions: Approval Event recorded. Pre-registration hash computed.
    Approved → In_Progress
      Trigger:       Investigator begins execution
      Preconditions: Required resources available (if tracked)
      Postconditions: Start Event recorded.
    In_Progress → Completed
      Trigger:       Results (Evidence) submitted
      Preconditions: At least one Evidence artifact linked as result
      Postconditions: Completion Event. Results linked to Hypotheses for
                      confidence update (triggers FLOW-K002).
    In_Progress → Abandoned
      Trigger:       Investigator or Steward abandons
      Preconditions: Abandonment rationale provided
      Postconditions: Abandonment Event. Partial results (if any) preserved.
    Designed → Abandoned
      Trigger:       Design found flawed or Question dissolved
      Preconditions: Abandonment rationale provided
      Postconditions: Abandonment Event recorded.

SM-K006: Epistemic Envelope Lifecycle — Entity: ENT-K022 — Source: ASM-K006
  States:      Created, Active, Suspended, Revoked
  Transitions:
    Created → Active
      Trigger:       Steward activates
      Preconditions: Agent identity verified. Human approver designated.
      Postconditions: Agent may begin operations within Envelope.
    Active → Suspended
      Trigger:       Kill switch activated OR cumulative threshold exceeded
                     OR manual suspension by Steward
      Preconditions: Suspension reason recorded
      Postconditions: All in-progress operations cancelled if possible.
                      No new operations. Suspension Event recorded.
    Suspended → Active
      Trigger:       Steward reviews and re-activates
      Preconditions: Root cause addressed. Re-activation rationale provided.
      Postconditions: Agent resumes. Re-activation Event recorded.
    Active → Revoked
      Trigger:       Steward permanently revokes
      Preconditions: Revocation rationale provided
      Postconditions: Envelope permanently inactive. All future requests rejected.
                      Revocation Event recorded.
    Suspended → Revoked
      Trigger:       Steward determines suspension should be permanent
      Preconditions: Revocation rationale provided
      Postconditions: Same as Active → Revoked
```

---


---

## 6. INTERFACES (SYSTEM SURFACES, NOT UI)

```
IFC-K001: Proposition CRUD — Implements: CAP-K001, CAP-K002, CAP-K003, CAP-K004
          — Source: SRC-K001
  Purpose:          Create, read, update (via Revision), and archive Propositions
  Auth requirement:  ACT-K001/K002/K003 (per Role), ACT-K004/K005 (per Envelope)
  Request schema:
    POST /orgs/{org_id}/propositions
      { content: text, formal_content?: expression, context_id: uuid,
        confidence: { value: decimal, lower: decimal, upper: decimal, method_id: uuid },
        domain_ids: [uuid], evidence_links?: [{ evidence_id: uuid, direction: enum,
        strength: enum }], tags?: [uuid] }
    GET /orgs/{org_id}/propositions/{id}
      Query params: ?as_of={datetime} (for time-travel, CAP-K005)
    PATCH /orgs/{org_id}/propositions/{id}/confidence
      { value: decimal, lower: decimal, upper: decimal, method_id: uuid,
        rationale: text, trigger_ref?: uuid }
      Header: If-Match: {etag}
    POST /orgs/{org_id}/propositions/{id}/retract
      { rationale: text, superseded_by?: uuid }
  Response schema:
    { id: uuid, content: text, ..., confidence: {...}, provenance: {...},
      contradiction_count: int, evidence_count: int, status: enum,
      authored_by_ai: bool, version: int, etag: string }
  Errors:            ERR-K001 (missing provenance), ERR-K002 (missing context),
                     ERR-K003 (envelope violation), ERR-K004 (invalid confidence),
                     ERR-K010 (authorization), ERR-K015 (optimistic lock conflict)
  Idempotency:       POST: via Idempotency-Key header (uuid, 30-day window)
  Pagination:        GET list: cursor-based, max 100 per page
  Rate limiting:     Per Actor per Envelope. Default 500 ops/min.

IFC-K002: Evidence Management — Implements: CAP-K007, CAP-K008, CAP-K009, CAP-K010
          — Source: SRC-K001, SRC-K011
  Purpose:          Submit, retrieve, and link Evidence to Propositions
  Auth requirement:  ACT-K001/K002/K003 (per Role), ACT-K004/K005 (per Envelope),
                     ACT-K006 (per Endpoint)
  Request schema:
    POST /orgs/{org_id}/evidence
      { content: text | blob_ref, content_type: mime, source_id: uuid,
        collection_method_id?: uuid, collection_context_id: uuid,
        quality_grade: enum, timestamp: datetime_with_uncertainty,
        proposition_links?: [{ proposition_id: uuid, direction: enum, strength: enum }] }
    GET /orgs/{org_id}/evidence/{id}
    POST /orgs/{org_id}/evidence/{id}/link
      { proposition_id: uuid, direction: supports|undermines, strength: enum }
  Response schema:
    { id: uuid, content: text | blob_ref, ..., status: enum, version: int, etag: string }
  Errors:            ERR-K001 (missing provenance), ERR-K002 (missing context),
                     ERR-K003 (envelope violation), ERR-K008 (immutable content),
                     ERR-K010 (authorization)
  Idempotency:       POST: Idempotency-Key header
  Pagination:        Cursor-based, max 100
  Rate limiting:     Per Actor. Default 500 ops/min.

IFC-K003: Inference Operations — Implements: CAP-K011, CAP-K013, CAP-K014
          — Source: SRC-K008
  Purpose:          Create and inspect Inferences (reasoning steps)
  Auth requirement:  ACT-K001/K002/K003 (per Role), ACT-K004/K005 (per Envelope)
  Request schema:
    POST /orgs/{org_id}/inferences
      { inputs: [{ type: proposition|evidence, id: uuid }], output_proposition_id: uuid,
        method_id: uuid, strength: enum, rationale: text,
        validity_conditions?: [uuid] }
    GET /orgs/{org_id}/inferences/{id}
    GET /orgs/{org_id}/inferences/{id}/chain
      Returns: full inference chain from this Inference to root Evidence/Propositions
  Response schema:
    { id: uuid, inputs: [...], output: {...}, method: {...}, strength: enum,
      authored_by_ai: bool, status: enum }
  Errors:            ERR-K003 (envelope violation), ERR-K005 (dependency cycle),
                     ERR-K006 (broken inference chain), ERR-K008 (opaque method),
                     ERR-K010 (authorization)
  Idempotency:       POST: Idempotency-Key header
  Rate limiting:     Per Actor. Default 200 ops/min (heavier validation).

IFC-K004: Contradiction Management — Implements: CAP-K006 — Source: ASM-K005
  Purpose:          View, acknowledge, and resolve Contradictions
  Auth requirement:  ACT-K001/K002/K003 (per Role), ACT-K004/K005 (read per Envelope)
  Request schema:
    GET /orgs/{org_id}/contradictions
      Query params: ?status={enum}&domain_id={uuid}&proposition_id={uuid}
    GET /orgs/{org_id}/contradictions/{id}
    POST /orgs/{org_id}/contradictions/{id}/resolve
      { method: text, rationale: text, chosen_proposition_id?: uuid }
    POST /orgs/{org_id}/contradictions/{id}/acknowledge
      { rationale: text }
  Response schema:
    { id: uuid, propositions: [...], type: enum, severity: enum,
      context: {...}, resolution_status: enum, resolution?: {...} }
  Errors:            ERR-K009 (missing rationale), ERR-K010 (authorization),
                     ERR-K011 (contradiction not found)
  Idempotency:       Resolve/acknowledge: Idempotency-Key header
  Rate limiting:     Default 500 ops/min.

IFC-K005: Query & View — Implements: CAP-K005, TERM-K024, TERM-K025 — Source: SRC-K005
  Purpose:          Structured knowledge retrieval with provenance
  Auth requirement:  Any authenticated Actor within permission scope
  Request schema:
    POST /orgs/{org_id}/query
      { scope: { domains?: [uuid], time_range?: { from: datetime, to: datetime },
        sources?: [uuid], confidence_min?: decimal, status_filter?: [enum] },
        content_search?: text, concept_tags?: [uuid],
        depth: surface|deep_inference, as_of?: datetime,
        response_format: propositions|arguments|evidence|summary,
        limit: int (max 1000), cursor?: string }
    GET /orgs/{org_id}/views/{view_id}
    POST /orgs/{org_id}/views
      { name: text, query: {...}, layout: enum(graph|table|timeline|
        dependency_map|contradiction_report|hypothesis_matrix|provenance_chain) }
  Response schema:
    { results: [...], total_count: int, cursor?: string,
      query_metadata: { domains_searched: [uuid], as_of: datetime, depth: enum } }
  Errors:            ERR-K010 (authorization), ERR-K012 (query timeout),
                     ERR-K013 (query too broad)
  Pagination:        Cursor-based, max 1000 per page
  Rate limiting:     Default 200 queries/min. Cost estimation for deep inference queries.

IFC-K006: Ontology Management — Implements: CAP-K016, CAP-K017, CAP-K018 — Source: SRC-K006
  Purpose:          Define, version, and align Ontologies
  Auth requirement:  ACT-K003 (admin), others (read)
  Request schema:
    POST /orgs/{org_id}/ontologies
      { name: text, description: text, domain_id: uuid,
        concepts: [{ name: text, definition: text, synonyms?: [text],
                     parent_ids?: [uuid] }],
        relations?: [{ source_concept_id: uuid, target_concept_id: uuid,
                       type: enum, direction: enum }],
        axioms?: [expression] }
    POST /orgs/{org_id}/ontologies/{id}/versions
      (new version with diff from previous)
    POST /orgs/{org_id}/ontologies/{id}/align
      { target_ontology_id: uuid,
        mappings: [{ source_concept_id: uuid, target_concept_id: uuid,
                     alignment: exact|broader|narrower|related, confidence: decimal }] }
    POST /orgs/{org_id}/ontologies/{id}/propagate-preview
      (dry-run of FLOW-K006 — returns affected Propositions without applying)
  Response schema:
    { id: uuid, name: text, ..., version: int, concept_count: int,
      relation_count: int, alignment_count: int }
  Errors:            ERR-K010 (authorization), ERR-K014 (axiom unsatisfiable),
                     ERR-K005 (cycle in taxonomy)
  Idempotency:       POST: Idempotency-Key header
  Rate limiting:     Default 100 ops/min (heavy operations).

IFC-K007: Argument Construction — Implements: CAP-K011, CAP-K015 — Source: SRC-K004
  Purpose:          Build, inspect, and challenge Arguments
  Auth requirement:  ACT-K001/K002/K003 (per Role), ACT-K004/K005 (per Envelope)
  Request schema:
    POST /orgs/{org_id}/arguments
      { name: text, premises: [{ type: proposition|evidence, id: uuid }],
        inference_chain: [uuid], conclusion_id: uuid, known_weaknesses: [text] }
    GET /orgs/{org_id}/arguments/{id}
    GET /orgs/{org_id}/arguments/{id}/counter-arguments
    — REMOVED: POST /orgs/{org_id}/arguments/{id}/challenge
      Challenges to Arguments are conducted via SUBSTRATE-COMMUNICATION. An agent
      creates an Objection Speech Act (COMMUNICATION TERM-M008) targeting this
      Argument via cross-substrate Reference (see CROSS-SUBSTRATE-CONVENTIONS.md §5).
      If the Objection is sustained (COMMUNICATION Resolution, TERM-M017), the
      originating agent or system may add a counter_argument to this Knowledge
      Argument or revise confidence. See CROSS-SUBSTRATE-CONVENTIONS.md §6 Principle P1.
  Response schema:
    { id: uuid, ..., strength: enum, known_weaknesses: [text],
      counter_arguments: [uuid], authored_by_ai: bool, status: enum }
  Errors:            ERR-K006 (broken chain), ERR-K007 (missing weaknesses),
                     ERR-K010 (authorization)
  Idempotency:       POST: Idempotency-Key header
  Rate limiting:     Default 200 ops/min.

IFC-K008: Inquiry Lifecycle — Implements: CAP-K019, CAP-K020, CAP-K021 — Source: SRC-K001
  Purpose:          Manage Questions, Hypotheses, and Experiments
  Auth requirement:  ACT-K001/K002/K003 (per Role), ACT-K005 (per Envelope)
  Request schema:
    POST /orgs/{org_id}/questions
      { content: text, presuppositions?: [uuid], domain_id: uuid, priority: enum }
    POST /orgs/{org_id}/questions/{id}/hypotheses
      { claim_proposition_id: uuid, prior_confidence: {...} }
    POST /orgs/{org_id}/experiments
      { name: text, question_id: uuid, hypotheses_tested: [uuid],
        protocol_method_id: uuid,
        predicted_outcomes: [{ hypothesis_id: uuid, predicted: text,
                               confidence_if_observed: decimal }] }
    POST /orgs/{org_id}/experiments/{id}/results
      { evidence_ids: [uuid] }
  Response schema:
    { id: uuid, ..., status: enum, hypotheses: [...],
      discriminating_evidence: [...] }
  Errors:            ERR-K010 (authorization), ERR-K015 (conflict),
                     ERR-K016 (insufficient hypotheses for experiment)
  Idempotency:       POST: Idempotency-Key header
  Rate limiting:     Default 200 ops/min.

IFC-K009: Source & Calibration — Implements: CAP-K027, TERM-K020, TERM-K021
          — Source: SRC-K004
  Purpose:          Register Sources, track Calibration, assess trust
  Auth requirement:  ACT-K003 (admin for trust changes), others (read)
  Request schema:
    POST /orgs/{org_id}/sources
      { name: text, type: enum, identity: text, domains_of_expertise?: [uuid],
        known_biases?: [text] }
    PATCH /orgs/{org_id}/sources/{id}/trust
      { trust_level: enum, rationale: text }
      Header: If-Match: {etag}
    POST /orgs/{org_id}/calibrations
      { subject_type: source|method, subject_id: uuid, domain_id: uuid,
        metric: enum, value: decimal, sample_size: int,
        period: { from: datetime, to: datetime } }
  Response schema:
    { id: uuid, ..., trust_level: enum, calibration_history: [...] }
  Errors:            ERR-K010 (authorization), ERR-K017 (insufficient sample size)
  Rate limiting:     Default 500 ops/min.

IFC-K010: Configuration — Implements: TERM-K022, system setup — Source: ASM-K006
  Purpose:          Manage Organization configuration: Domains, Ontologies, Envelopes,
                    quality thresholds, propagation policies
  Auth requirement:  ACT-K003 only
  Request schema:
    POST /orgs
      { name: text, jurisdictions: [...], default_domains: [...] }
    GET /orgs/{org_id}/config
    PATCH /orgs/{org_id}/config
      { propagation_depth_limit?: int, propagation_breadth_limit?: int,
        default_confidence_ceiling_unverified?: decimal,
        cumulative_ai_change_threshold?: decimal,
        auto_accept_from_verified_sources?: bool }
  Response schema:
    { org_id: uuid, config: {...}, version: int }
  Errors:            ERR-K010 (authorization)
  Rate limiting:     50 ops/min (admin operations).

IFC-K011: Event Stream — Implements: ASM-K008, INV-K003 — Source: ASM-K008
  Purpose:          Subscribe to real-time Revision events for integration and monitoring
  Auth requirement:  Any authenticated Actor within permission scope
  Request schema:
    WebSocket: ws://host/orgs/{org_id}/events/stream
      Filter: { domains?: [uuid], event_types?: [enum], entity_types?: [enum] }
    HTTP polling: GET /orgs/{org_id}/events?after={sequence}&limit={int}
  Response schema:
    { events: [{ id: uuid, sequence: int, type: enum, target_id: uuid,
      target_type: enum, actor_id: uuid, timestamp: datetime, payload: {...},
      hash: text, prev_hash: text }], cursor: string }
  Errors:            ERR-K010 (authorization), ERR-K012 (timeout)
  Rate limiting:     WebSocket: 1 connection per Actor. Polling: 60 requests/min.

IFC-K012: Data Export — Implements: CAP-K024 — Source: NG-K003
  Purpose:          Bulk export of all knowledge artifacts in open formats
  Auth requirement:  ACT-K003 only
  Request schema:
    POST /orgs/{org_id}/export
      { scope: { domains?: [uuid], time_range?: {...}, entity_types?: [enum] },
        format: json|csv|rdf_turtle|jsonld }
  Response schema:
    Async: { export_id: uuid, status: pending|in_progress|complete|failed }
    GET /orgs/{org_id}/exports/{export_id}/download → binary stream
  Errors:            ERR-K010 (authorization), ERR-K012 (timeout)
  Rate limiting:     1 concurrent export per Organization.

IFC-K013: Approval Routing — Implements: FLOW-K007, CAP-K022 — Source: ASM-K006
  Purpose:          Human review and approval for AI agent actions exceeding Envelope
  Auth requirement:  Designated human_approver from Epistemic Envelope
  Request schema:
    GET /orgs/{org_id}/approvals/pending
      Query params: ?assignee={actor_id}
    POST /orgs/{org_id}/approvals/{id}/approve
      { rationale: text }
    POST /orgs/{org_id}/approvals/{id}/reject
      { rationale: text }
  Response schema:
    { id: uuid, proposed_action: {...}, agent_id: uuid, envelope_id: uuid,
      threshold_exceeded: text, affected_propositions: [uuid],
      confidence_change_magnitude: decimal, status: enum, created_at: datetime }
  Errors:            ERR-K010 (authorization), ERR-K018 (approval expired)
  Rate limiting:     Default 500 ops/min.
```

---


---

## 7. DATA FLOWS (HOW THINGS HAPPEN)

```
FLOW-K001: Create Proposition — Implements: CAP-K001, CAP-K002, CAP-K006
  Trigger:             Actor submits new Proposition via API
  Inputs:              content, context, initial confidence assessment, evidence links,
                       domain, tags
  Steps:
    1. Validate Actor permissions (per Domain scope)
    2. Validate Provenance: creator MUST be identified, method SHOULD be specified
    3. Validate Context: at least one scope dimension specified
    4. Validate Confidence: value in [0,1], lower ≤ value ≤ upper, method specified
    5. If Actor is AI agent: verify Epistemic Envelope permits propose_proposition
       in specified Domain; set authored_by_ai = true (immutable)
    6. Store Proposition with status = Draft
    7. Run Contradiction Detection: compare against existing Propositions in same
       Context using configured detection methods
    8. If Contradictions detected: create ENT-K009 instances, link to Proposition,
       notify relevant Actors
    9. Record creation Event (hash-chained)
    10. If automation rules configured: trigger (e.g., notify domain experts,
        queue for peer review, propagate to dependent systems)
  Outputs:             Proposition UUID, detected Contradictions (if any)
  Side effects:        Contradiction notifications. Dependency graph updated.
  Error paths:         Step 2 fail → ERR-K001 (missing provenance)
                       Step 3 fail → ERR-K002 (missing context)
                       Step 5 fail → ERR-K003 (envelope violation)
  Atomicity:           Proposition creation + Contradiction detection are atomic.
                       Notifications are async side effects (FAIL-K004 applies).

FLOW-K002: Update Confidence — Implements: CAP-K003, CAP-K012
  Trigger:             New Evidence linked, new Inference created, Actor manual update,
                       or propagation from dependent Proposition
  Inputs:              Proposition ref, new Confidence assessment, trigger reference
  Steps:
    1. Validate Actor permissions
    2. If Actor is AI agent: check Epistemic Envelope
       a. Check confidence_change_threshold: if |new - old| > threshold,
          route to human_approver (FLOW-K007)
    3. Validate new Confidence value
    4. Create Revision record (ENT-K010) with old state, new state, trigger, rationale
    5. Update Proposition's current confidence
    6. Identify all Propositions that depend on this one (Dependency Graph traversal)
    7. For each dependent Proposition: schedule FLOW-K002 (recursive propagation)
       a. Propagation depth bounded by configurable max (default: 10 levels)
       b. Propagation breadth bounded by configurable max (default: 10,000 affected)
       c. If bounds exceeded: flag for human review, continue with affected set
    8. Re-run Contradiction Detection for affected Propositions
    9. Record Revision Event (hash-chained)
  Outputs:             Updated Confidence, Revision UUID, propagation report
  Error paths:         Step 2a → routed to approval (not error, but flow redirect)
                       Step 7c → WARN-K001 (propagation bounds exceeded)
  Atomicity:           Single Proposition update is atomic. Propagation is eventually
                       consistent (each hop is its own atomic update).

FLOW-K003: Detect Contradiction — Implements: CAP-K006
  Trigger:             New Proposition created, Confidence updated, or manual request
  Inputs:              Proposition ref, Context
  Steps:
    1. Retrieve all Propositions in same Context with confidence > configured threshold
    2. For each pair: evaluate logical consistency using configured Methods
       a. Formal: check if Proposition A AND Proposition B is satisfiable
       b. Statistical: check if Proposition A's evidence and Proposition B's evidence
          are statistically compatible
       c. Heuristic: check for known contradiction patterns (configured per Domain)
    3. For detected conflicts: create ENT-K009 (Contradiction) with type and severity
    4. Notify affected Proposition authors and domain stewards
    5. Record detection Event
  Outputs:             List of new Contradictions (if any)
  Error paths:         Formal consistency check timeout → fall back to heuristic.
                       No configured detection method for Domain → skip, log warning.
  Atomicity:           Per Proposition-pair check. No global lock.

FLOW-K004: Build Argument — Implements: CAP-K011
  Trigger:             Actor constructs reasoning chain
  Inputs:              Premises (Propositions + Evidence), Inference steps, Conclusion
  Steps:
    1. Validate Actor permissions
    2. Validate each premise exists and is accessible to Actor
    3. Validate each Inference step: inputs match stated, Method is valid
    4. Validate chain connectivity: premises → inference₁ → ... → inferenceₙ → conclusion
    5. Assess Argument strength (weakest link in inference chain)
    6. Require known_weaknesses to be non-empty
    7. Store Argument with status = Proposed
    8. Link conclusion Proposition to this Argument
    9. If counter-arguments exist for conclusion: link as counter_arguments
    10. Record creation Event
  Outputs:             Argument UUID, assessed strength, linked counter-arguments
  Error paths:         Step 4 fail → ERR-K006 (broken inference chain)
                       Step 6 fail → ERR-K007 (missing weakness acknowledgment)
  Atomicity:           Argument creation is atomic.

FLOW-K005: Execute Inquiry Cycle — Implements: CAP-K019, CAP-K020, CAP-K021
  Trigger:             Actor opens Question
  Inputs:              Question content, presuppositions, domain
  Steps:
    1. Create Question (ENT-K016)
    2. Search existing Propositions for potential answers (Query)
    3. If existing Propositions found with sufficient confidence: suggest as Hypotheses
    4. Actor (or AI agent within Envelope) proposes Hypotheses
    5. For each Hypothesis: assess prior confidence, identify competing Hypotheses
    6. Design discriminating Experiments: identify Evidence that would most change
       relative confidence between Hypotheses
    7. Execute Experiments (external — results enter as Evidence via FLOW-K001)
    8. Update Hypothesis confidences based on results (FLOW-K002)
    9. When one Hypothesis exceeds Domain's confidence threshold with sufficient
       Evidence: Question status → answered
    10. Record full inquiry trail as linked Events
  Outputs:             Answered Question (or ongoing investigation status)
  Side effects:        All intermediate artifacts (Hypotheses, Experiments, Evidence)
                       are first-class objects — the inquiry trail IS knowledge.
  Error paths:         Step 9 never reached → Question remains open (this is normal,
                       not an error)
  Atomicity:           Each step is independently atomic. The full cycle is a workflow,
                       not a transaction.

FLOW-K006: Propagate Ontology Change — Implements: CAP-K016, CAP-K017
  Trigger:             Ontology version published (Concept added, removed, or Relations changed)
  Inputs:              Old Ontology version, new Ontology version, diff
  Steps:
    1. Compute diff: added Concepts, removed Concepts, changed Relations
    2. For removed Concepts: find all Propositions tagged with that Concept
       a. Re-tag to nearest parent Concept (if exists) or flag for human review
    3. For changed Relations: re-evaluate Inferences that relied on the old Relation
    4. For added Concepts: check if existing Propositions should be tagged
    5. Update cross-Ontology Alignment mappings affected by changes
    6. Record Ontology change Event with full diff
    7. Notify domain stewards
  Outputs:             Migration report (affected Propositions, re-tagged, flagged)
  Error paths:         Step 2a no parent → flag for human; do NOT auto-delete tags
  Atomicity:           Per-Concept migration is atomic. Full Ontology migration is
                       eventually consistent.

FLOW-K007: Route to Human Approval (via COMMUNICATION) — Implements: CAP-K022
  Trigger:             AI agent action exceeds Epistemic Envelope threshold
  Inputs:              Proposed action, agent ref, envelope ref, threshold exceeded
  Steps:
    1. Suspend proposed action
    2. Knowledge system constructs approval request: { proposed_action,
       agent_ref, envelope_ref, threshold_exceeded, affected_propositions,
       confidence_change_magnitude, context_summary }
    3. Emit event: approval_requested to COMMUNICATION via shared event bus
       (topic: substrate.knowledge.envelope.approval_requested)
    4. COMMUNICATION creates Discourse with Protocol "epistemic_approval"
       between agent's principal (human approver) and system
    5. Approver receives Directive Speech Act (COMMUNICATION TERM-M006) with
       approval request details
    6. Approver responds: Acknowledgment (approve) or Objection (reject)
       with rationale
    7. COMMUNICATION emits event: approval_resolved with outcome
       (topic: substrate.communication.discourse.approval_resolved)
    8. Knowledge system consumes outcome:
       - If approved: execute original action with attribution to both agent
         and approver
       - If rejected: action blocked, agent notified, rejection reason recorded
       - If timeout: reject by default; record timeout
  Outputs:             Approval decision
  Fallback:            If COMMUNICATION unavailable: queue approval request locally.
                       Apply conservative default (reject) until COMMUNICATION recovers.
  Timeout:             Configurable (default: 72h). If timeout: reject by default.
  Error paths:         Approver unavailable → escalate to Organization admin
                       COMMUNICATION down → local queue + conservative reject
  Atomicity:           Approval decision is atomic.
  Cross-substrate:     See CROSS-SUBSTRATE-CONVENTIONS.md §3 (Event Bus), §4 (Tracing).
```

---


---

## 8. INTEGRATION CONTRACTS (EXTERNAL SYSTEMS)

```
INT-K001: Source Registry — Depends on: DEP-K003 — Source: SRC-K007
  Protocol:          REST (JSON)
  Auth:              Mutual TLS + API key
  Request format:    GET /sources/{identifier} — lookup by DOI, ISSN, ORCID, ROR, or UUID
  Response format:   { source_id, name, type, reliability_metadata, domains, last_updated }
  Failure modes:     Timeout (>2s) / 4xx (unknown source) / 5xx (registry down) / rate-limited
  Retry policy:      3 retries, exponential backoff 1s/3s/10s. Circuit breaker: open after
                     5 failures in 60s; half-open at 120s.
  Idempotency:       Safe (read-only lookups)
  Partial success:   N/A — binary (found or not)

INT-K002: Computation Backend — Depends on: DEP-K004 — Source: SRC-K008
  Protocol:          gRPC (for performance on large inference graphs) or REST fallback
  Auth:              Service account + mutual TLS
  Request format:    InferenceRequest { method_id, inputs: [...], parameters: {...},
                     timeout_ms: int }
  Response format:   InferenceResult { output_confidence: decimal, computation_trace: [...],
                     execution_time_ms: int }
  Failure modes:     Timeout (configurable, default 30s) / resource exhaustion /
                     unsupported method / numerical instability
  Retry policy:      Non-deterministic computations (MCMC, etc.): NO automatic retry.
                     Deterministic computations: 2 retries, 5s/15s backoff.
                     Circuit breaker: open after 3 failures in 120s; half-open at 300s.
  Idempotency:       Deterministic methods: safe to retry. Stochastic methods: NOT safe
                     (may produce different samples). Use computation_id for dedup.
  Partial success:   Computation may converge partially — return partial result with
                     convergence status. System uses partial result with wider uncertainty bounds.

INT-K003: Content Store — Depends on: DEP-K006 — Source: SRC-K001, SRC-K011
  Protocol:          S3-compatible API / content-addressable store
  Auth:              IAM role / service account / signed URLs
  Request format:    PUT: binary content + content-type + metadata.
                     GET: blob reference → binary stream.
  Response format:   PUT: { blob_ref, size, checksum_sha256 }. GET: binary stream.
  Failure modes:     Timeout / 5xx / storage full / blob not found / checksum mismatch
  Retry policy:      3 retries, 2s/5s/15s backoff. Upload: verify checksum after each retry.
                     Circuit breaker: open after 5 failures in 120s; half-open at 60s.
  Idempotency:       Content-addressable: same content = same ref. Safe to retry.
  Partial success:   Multipart upload: resume from last confirmed chunk.

INT-K004: Communication Delivery — Depends on: DEP-K005 — Source: SRC-K001
  Protocol:          SMTP (email) / webhook (HTTP POST) / push notification / in-system
  Auth:              Per-channel: SMTP auth / HMAC-signed webhook / API key
  Request format:    Per-channel standard formats
  Response format:   Delivery receipt or async status callback
  Failure modes:     Timeout / bounce / invalid recipient / rate-limited / channel down
  Retry policy:      3 retries, 1m/5m/30m backoff. After 3 failures: "delivery_failed."
                     TTL: Notifications expire after 72h default.
  Idempotency:       Webhook: idempotency key in header. Email: not safely retryable (may dupe).
  Partial success:   Multi-channel: each independent. Failure on one doesn't block others.

INT-K005: SUBSTRATE (Business) Interop — Depends on: DEP-K007 — Source: INTEROP-001 through 004
  Protocol:          REST (SUBSTRATE API) + shared event bus
  Auth:              Service-to-service mutual TLS + scoped API token
  Request format:    Standard SUBSTRATE API calls (see SUBSTRATE openapi.json)
  Response format:   Standard SUBSTRATE API responses
  Failure modes:     SUBSTRATE unavailable / entity not found / permission denied /
                     schema version mismatch
  Retry policy:      3 retries, 2s/5s/15s. Circuit breaker: open after 5 failures in 60s.
  Idempotency:       Per SUBSTRATE's Idempotency-Key header.
  Partial success:   Knowledge operations continue independently. Cross-references marked
                     "unresolvable" until SUBSTRATE recovers. Auto-resolve on recovery.

INT-K006: Identity Verification — Depends on: DEP-K002 — Source: SRC-K013
  Protocol:          OpenID Connect / SAML 2.0 / WebAuthn
  Auth:              Mutual TLS between SUBSTRATE-KNOWLEDGE and identity provider
  Request format:    Standard OIDC/SAML auth request
  Response format:   ID token (JWT) with claims: sub, org, roles, exp, iat
  Failure modes:     Provider down / token expired / invalid signature / clock skew
  Retry policy:      3 retries, 1s/2s/4s. Circuit breaker: open after 5 failures in 60s;
                     half-open at 60s.
  Idempotency:       Safe to retry (verification is read-only)
  Partial success:   N/A — binary

INT-K007: KNOWLEDGE ↔ COMPUTE Integration
  Purpose:    Register computational results as epistemic evidence and provide
              knowledge-backed parameters for computation.
  Protocol:
    — Event-driven via shared event bus + REST API for evidence creation.
    — KNOWLEDGE emits: substrate.knowledge.proposition.confidence_changed
      (may trigger recomputation), substrate.knowledge.inference.completed.
    — COMPUTE emits: substrate.compute.execution.completed,
      substrate.compute.job.completed (results available as evidence).
  Delegation:
    — COMPUTE Execution (TERM-C006) results become KNOWLEDGE Evidence (TERM-K002)
      artifacts. COMPUTE owns execution and provenance. KNOWLEDGE owns epistemic
      interpretation (Confidence assignment, Proposition linkage).
    — KNOWLEDGE Propositions (TERM-K001) provide parameters for COMPUTE Pipelines
      (e.g., probability distributions, material constants, calibration data).
    — COMPUTE Provenance (TERM-C018) maps to KNOWLEDGE Provenance (TERM-K005)
      for end-to-end traceability.
  Boundary: COMPUTE owns computation execution and results. KNOWLEDGE owns epistemic
            interpretation and confidence. Principle P1.
            This is the KNOWLEDGE-side mirror of INT-C007.

INT-K008: KNOWLEDGE ↔ COMMUNICATION Integration
  Purpose:    Ingest discourse products as propositions and provide knowledge context
              for discourse references.
  Protocol:
    — Event-driven via shared event bus + REST API for knowledge reference resolution.
    — KNOWLEDGE emits: substrate.knowledge.proposition.confidence_changed,
      substrate.knowledge.proposition.retracted,
      substrate.knowledge.contradiction.detected.
    — COMMUNICATION emits: substrate.communication.discourse.resolved
      (consensus products available for epistemic ingestion),
      substrate.communication.discourse.approval_resolved.
  Delegation:
    — COMMUNICATION Discourse (TERM-M001) consensus products promote to KNOWLEDGE
      Propositions (TERM-K001). COMMUNICATION owns discourse process.
      KNOWLEDGE owns truth assessment.
    — KNOWLEDGE provides Proposition summaries and Confidence values for
      cross-substrate reference resolution (CONVENTIONS §5) within Speech Acts.
    — Discourse approval routing for Epistemic Envelope changes uses
      COMMUNICATION as delivery mechanism. KNOWLEDGE owns approval semantics.
  Boundary: COMMUNICATION owns discourse structure. KNOWLEDGE owns propositional
            content and confidence. Principle P1.
            This is the KNOWLEDGE-side mirror of INT-M004.

INT-K009: KNOWLEDGE ↔ TEMPORAL Integration
  Purpose:    Provide duration estimates and demand forecasts as epistemic knowledge;
              receive temporal outcome data to refine models.
  Protocol:
    — Event-driven via shared event bus.
    — KNOWLEDGE emits: substrate.knowledge.proposition.confidence_changed
      (duration estimate revised), substrate.knowledge.inference.completed
      (new forecast available).
    — TEMPORAL emits: substrate.temporal.activity.completed (actual duration
      for model update), substrate.temporal.capacity.gap_detected.
  Delegation:
    — KNOWLEDGE Propositions (TERM-K001) express duration estimates, demand
      forecasts, and no-show probability models. TEMPORAL consumes as planning
      parameters (Activity duration, Capacity demand, overbooking models).
    — TEMPORAL Activity completions (with actual duration) flow back to KNOWLEDGE
      as Observations (TERM-K019) to update duration distribution models.
    — v1.1 stochastic support: TEMPORAL Activity.knowledge_proposition_ref
      enables full probability distribution integration.
  Boundary: KNOWLEDGE owns estimates and their confidence. TEMPORAL owns scheduling
            decisions. Principle P1.
            This is the KNOWLEDGE-side mirror of INT-T006.

INT-K010: KNOWLEDGE ↔ SPATIAL Integration
  Purpose:    Attach geographic provenance to knowledge sources and observations;
              register spatial accuracy claims as epistemic propositions.
  Protocol:
    — Event-driven via shared event bus + cross-substrate reference resolution.
    — KNOWLEDGE Source (TERM-K020) and Observation (TERM-K019) MAY carry
      location_ref → SPATIAL Location for geographic provenance.
    — SPATIAL SpatialAccuracy (TERM-S029) MAY link to KNOWLEDGE Proposition
      for accuracy claims entering the epistemic record.
  Delegation:
    — KNOWLEDGE owns epistemic structure (what is known, with what confidence).
      SPATIAL owns geographic vocabulary (where it was observed/measured).
    — Geographic provenance enhances KNOWLEDGE Source reliability assessment:
      proximity to observed phenomenon affects epistemic weight.
  Boundary: KNOWLEDGE owns truth claims. SPATIAL owns location representation.
            Principle P4 (KNOWLEDGE owns claim, SPATIAL provides geographic context).
            This is the KNOWLEDGE-side mirror of INT-S007.

INT-K011: KNOWLEDGE ↔ PHYSICAL Integration
  Purpose:    Register physical sensors as knowledge sources and physical measurements
              as epistemic observations.
  Protocol:
    — Event-driven via shared event bus.
    — KNOWLEDGE emits: substrate.knowledge.source.reliability_changed,
      substrate.knowledge.proposition.confidence_changed.
    — PHYSICAL emits: substrate.physical.measurement.quality_changed,
      substrate.physical.calibration.completed,
      substrate.physical.hazard_analysis.reviewed,
      substrate.physical.digital_twin.drift_detected.
  Delegation:
    — PHYSICAL Sensor → KNOWLEDGE Source (TERM-K020): sensor registered as
      knowledge source. Calibration history provides reliability metadata.
    — PHYSICAL Measurement → KNOWLEDGE Observation (TERM-K019): raw measurement
      with quality metadata becomes epistemic observation.
    — PHYSICAL Calibration (TERM-P006) ↔ KNOWLEDGE Calibration (TERM-K021):
      hardware accuracy + epistemic reliability = complete trust chain.
    — PHYSICAL HazardAnalysis → KNOWLEDGE Proposition: risk assessment validity
      tracked as epistemic claim.
    — PHYSICAL DigitalTwin → KNOWLEDGE prediction accuracy as Proposition.
  Boundary: PHYSICAL owns hardware truth and control. KNOWLEDGE owns epistemic
            interpretation and confidence. Principle P1.
            This is the KNOWLEDGE-side mirror of INT-P002.

INT-K012: KNOWLEDGE ↔ DESIGN Integration
  Purpose:    Provide material property knowledge for design decisions and register
              design analysis results as epistemic observations.
  Protocol:
    — Event-driven via shared event bus.
    — KNOWLEDGE emits: substrate.knowledge.proposition.confidence_changed
      (material property updated), substrate.knowledge.evidence.new_evidence.
    — DESIGN emits: substrate.design.analysis.completed (results available
      as epistemic observations), substrate.design.constraint.violated
      (may contradict material property Propositions).
  Delegation:
    — KNOWLEDGE Propositions (TERM-K001) express material properties with
      Confidence. DESIGN consumes and cites (Principle P1).
    — DESIGN AnalysisResult → KNOWLEDGE Observation (TERM-K019): simulation
      and test results enter the epistemic record.
    — DESIGN DesignRationale references KNOWLEDGE Argument (TERM-K015).
    — Standards registered as KNOWLEDGE Sources (TERM-K020), referenced by
      DESIGN as Constraints.
    — If design testing contradicts a material property: DESIGN emits event;
      KNOWLEDGE evaluates as potential contradiction.
    — DESIGN DesignSpace (TERM-D026) exploration may map to KNOWLEDGE
      Hypothesis (TERM-K009) + Experiment (TERM-K010).
  Boundary: KNOWLEDGE owns truth about materials and science. DESIGN owns
            design application. Principle P1.
            This is the KNOWLEDGE-side mirror of INT-D002.

INT-K013: KNOWLEDGE ↔ GOVERNANCE Integration
  Purpose:    Model normative content as epistemic propositions and provide calibrated
              confidence for compliance evidence.
  Protocol:
    — Event-driven via shared event bus.
    — KNOWLEDGE emits: substrate.knowledge.proposition.confidence_changed,
      substrate.knowledge.proposition.retracted,
      substrate.knowledge.evidence.new_evidence.
    — GOVERNANCE emits: substrate.governance.norm.effective (KNOWLEDGE may
      describe normative content as Proposition),
      substrate.governance.risk.assessed.
  Delegation:
    — GOVERNANCE Norm (TERM-G001) prescriptive content → KNOWLEDGE may model
      as descriptive Proposition (TERM-K001). GOVERNANCE owns prescriptive force.
      KNOWLEDGE owns descriptive truth. Principle P1.
    — GOVERNANCE risk likelihood → KNOWLEDGE Confidence (TERM-K003) + Evidence
      (TERM-K002). GOVERNANCE wraps in risk context (impact, controls, tolerance).
      KNOWLEDGE provides calibrated confidence where available.
    — GOVERNANCE ComplianceAssessment confidence → KNOWLEDGE calibration
      methodology. KNOWLEDGE provides calibration, GOVERNANCE owns assessment.
    — AI-generated knowledge status (OQ-K003): GOVERNANCE Norms define per-
      Jurisdiction status. KNOWLEDGE queries. Principle P3.
  Boundary: GOVERNANCE owns prescriptive norms. KNOWLEDGE owns descriptive truth
            and confidence calibration. Principle P1 (content/process split).
            This is the KNOWLEDGE-side mirror of INT-G002.
```

**Cross-substrate event topics emitted by SUBSTRATE-KNOWLEDGE:**

```
substrate.knowledge.proposition.created              — New Proposition entered into epistemic record
substrate.knowledge.proposition.confidence_changed   — Proposition Confidence revised (up or down)
substrate.knowledge.proposition.status_changed       — Alias for confidence_changed (backward compat)
substrate.knowledge.proposition.retracted            — Proposition withdrawn from active record
substrate.knowledge.evidence.new_evidence            — New Evidence linked to existing Proposition
substrate.knowledge.source.reliability_changed       — Source reliability metadata updated
substrate.knowledge.contradiction.detected           — Contradiction detected between Propositions
substrate.knowledge.inference.completed              — Inference engine produced new result
substrate.knowledge.envelope.approval_requested      — Epistemic Envelope change awaiting approval
substrate.knowledge.envelope.approval_resolved       — Epistemic Envelope approval completed
```

**Correlated failure scenarios:**

```
DEP-K002 + DEP-K004 fail simultaneously:
  System enters read-only mode for new Inferences requiring computation.
  Existing sessions continue until expiry. Simple expression evaluation continues.
  Proposition CRUD unaffected. Confidence propagation degraded (simple-only).

DEP-K003 + DEP-K006 fail simultaneously:
  Core operations continue. New Source registration blocked — unverified Sources accepted
  with minimum confidence floor. Evidence metadata accessible, content unavailable.

DEP-K004 + DEP-K007 fail simultaneously:
  Knowledge operations continue independently. Cross-SUBSTRATE references unresolvable.
  Complex inferences queue. Simple knowledge CRUD fully operational.

All DEPs fail (catastrophic):
  Edge nodes continue in offline mode (CAP-K026). All writes queued locally.
  Read operations use local cache. Confidence propagation paused.
  Full functionality restored on recovery via offline sync.
```

---


---

## 9. AUTHORIZATION & ACCESS MODEL

### Roles / Actors

Reference: ACT-K001 through ACT-K007 (Section 1).

### Resources

```
RES-K001: Proposition (per Domain)           — maps to: ENT-K001
RES-K002: Evidence                           — maps to: ENT-K002
RES-K003: Inference                          — maps to: ENT-K006
RES-K004: Ontology (schema management)       — maps to: ENT-K013
RES-K005: Argument                           — maps to: ENT-K015
RES-K006: Question                           — maps to: ENT-K016
RES-K007: Experiment                         — maps to: ENT-K018
RES-K008: Source (registration & trust)      — maps to: ENT-K020
RES-K009: Calibration                        — maps to: ENT-K021
RES-K010: Configuration (system setup)       — maps to: IFC-K010
RES-K011: Epistemic Envelope                 — maps to: ENT-K022
RES-K012: Data Export                        — maps to: IFC-K012
RES-K013: Audit / Belief Time-Travel Query   — maps to: IFC-K005 (as_of parameter)
RES-K014: Contradiction (resolution)         — maps to: ENT-K009
RES-K015: Approval (routing decisions)       — maps to: IFC-K013
```

### Ownership Rules

```
OWN-K001: Propositions — Creator has full CRUD. Others in same Domain have read.
          Update/archive requires creator OR Steward OR Domain-specific Role grant.
          Retraction requires creator OR Steward.
OWN-K002: Evidence — Creator has full CRUD until Active. After Active, content is
          immutable (INV-K009). Only Steward can deprecate.
OWN-K003: Ontologies — Steward only for create/update/publish. All others read.
OWN-K004: Contradictions — System creates (automatic detection). Any Actor in scope
          can read. Only Actors with write permission on BOTH conflicting Propositions
          (or Steward) can resolve.
OWN-K005: Epistemic Envelopes — Steward creates, modifies, activates, suspends, revokes.
          Designated human_approver can approve/reject routed actions.
          Agent has read access to own Envelope.
```

### Delegation & Elevation

```
DEL-K001: Steward (ACT-K003) may grant Domain-scoped Roles to any Actor.
          Grants are audited. Grants expire at configured time (default: 365 days).
DEL-K002: Steward may designate deputy Stewards with subset of admin permissions.
DEL-K003: Epistemic Envelope human_approver may be reassigned by Steward.
          During reassignment, pending approvals transfer to new approver.
DEL-K004: Cross-Organization access grants: Steward of granting Org creates a
          scoped, revocable, time-limited sharing agreement specifying:
          Domain scope, Entity types shared, permission level (read-only or read+annotate).
```

### Unauthenticated Access

No unauthenticated access is permitted. All API calls require a valid Bearer token. Rationale: knowledge provenance requires actor attribution for every operation (INV-K001); anonymous access would violate this invariant. Public knowledge (e.g., open-access publications) is accessed through authenticated sessions; the Actor performing the query is logged, not the original Author.

### Session / Token Model

```
SESSION-K001: Authentication via OIDC/SAML → JWT access token + refresh token.
  Access token: 15-minute expiry. Contains: sub, org_id, roles, domain_scope.
  Refresh token: 7-day expiry. Single-use (rotation on each refresh).
  Revocation: immediate via token revocation endpoint. Propagated within 60s.
  AI Agent sessions: separate token type with Envelope ID embedded. Non-refreshable.
  Agent token expiry: configurable per Envelope (default: 1 hour).
```

### Multi-tenancy

```
TENANT-K001: Organization-scoped isolation.
  Model: logical isolation with Organization ID in every primary key path.
  Cross-org query: returns empty set for non-shared data (no error — INV-K011).
  Cross-org sharing: requires explicit sharing agreement (DEL-K004).
  Tenant-scoping enforcement: at query layer (every query adds implicit
    WHERE org_id = {session.org_id}), NOT at application layer.
  Shared Ontologies: Ontology structure (Concepts, Relations) may be shared
    across Organizations via publishing. Propositions referencing shared Ontologies
    remain Organization-scoped.
```

---


### Permission Matrix

| | Proposition | Evidence | Inference | Ontology | Argument | Question | Experiment | Source | Calibration | Config |
|---|---|---|---|---|---|---|---|---|---|---|
| **ACT-K001** (Researcher) | CRUD* | CRUD* | CRUD* | read | CRUD* | CRUD* | CRUD* | read | read | none |
| **ACT-K002** (Analyst) | CRUD* | CRUD* | CRUD* | read | CRUD* | CRUD* | read | read | read | none |
| **ACT-K003** (Steward) | admin | admin | admin | admin | admin | admin | admin | admin | admin | admin |
| **ACT-K004** (Narrow AI) | per Envelope | per Envelope | per Envelope | read | per Envelope | read | none | read | read | none |
| **ACT-K005** (General AI) | per Envelope | per Envelope | per Envelope | read | per Envelope | per Envelope | per Envelope | read | read | none |
| **ACT-K006** (External) | per Endpoint | per Endpoint | none | read | none | none | none | per Endpoint | none | none |
| **ACT-K007** (Auditor) | read-all | read-all | read-all | read-all | read-all | read-all | read-all | read-all | read-all | read-all |

\* = filtered by Role-based Permissions within Organization and Domain scope


---

## 10. SECURITY & PRIVACY MODEL

### Data Classification

```
CLASS-K001: PII — Entities: Source (when type=human_agent), Provenance (creator field
            when human), Annotation (author), Consensus (participants)
            Treatment: field-level encryption, access logging, right-to-erasure via
            cryptographic shredding

CLASS-K002: Sensitive Knowledge — Entities: Propositions in Domains configured as
            sensitive (e.g., classified intelligence, medical records, trade secrets)
            Treatment: field-level encryption with Domain-specific keys, additional
            access logging, no bulk export without Steward approval

CLASS-K003: Internal — Entities: Epistemic Envelopes (configuration), Organization
            config, approval routing rules
            Treatment: standard encryption at rest, access limited to ACT-K003

CLASS-K004: Public — Entities: Published Ontologies (structure only), Domain definitions,
            Method definitions (formal specs)
            Treatment: standard encryption at rest, readable by all authenticated Actors
            within Organization (and cross-Org if published)
```

### Abuse Cases

```
ABUSE-K001: Epistemic flooding — mass Proposition creation to overwhelm contradiction
            detection and bury legitimate knowledge
  Given:    ACT-K001 or ACT-K004 with create permission
  When:     >5,000 Propositions created per hour from single Actor
  Then:     Rate limiter engages. Actor throttled. Alert to ACT-K003.
            Audit Event logged. Propositions created during flood flagged for review.

ABUSE-K002: Confidence salami-slicing — AI Agent makes many small confidence updates
            that individually pass threshold but cumulatively are significant
  Given:    ACT-K004 with confidence_change_threshold = 0.1
  When:     Agent makes 20 updates of Δ0.05 each within configured window (default: 24h)
  Then:     Cumulative change tracking triggers alert at configured cumulative
            threshold (default: 0.3). Agent suspended on this Proposition.
            Pending re-evaluation routed to human approver.

ABUSE-K003: Provenance laundering — routing low-trust claims through multiple
            intermediary Sources to inflate apparent reliability
  Given:    ACT-K006 submits Proposition citing Source A, which cites Source B, which
            cites Source C (the actual low-trust origin)
  When:     Provenance chain analyzed
  Then:     Confidence ceiling applied based on WEAKEST link in chain (Source C's
            trust level), not most recent Source. Alert if chain depth > configured
            maximum (default: 5 hops). Laundering pattern detected → alert to Steward.

ABUSE-K004: Contradiction suppression via resolution abuse — Actor repeatedly resolves
            Contradictions in favor of one side without engaging with counter-evidence
  Given:    ACT-K001 resolves 5+ Contradictions in the same direction within 7 days
  When:     Pattern detected
  Then:     Alert to ACT-K003 (Steward). Subsequent resolutions by this Actor require
            Steward co-approval until pattern review complete.

ABUSE-K005: Ontology sabotage — malicious Ontology change that cascades re-tagging
            to corrupt Proposition classification at scale
  Given:    ACT-K003 publishes Ontology version with destructive concept removal
  When:     Propagation preview (IFC-K006 dry-run) shows >1000 affected Propositions
  Then:     Propagation blocked. Requires second Steward approval. Dry-run results
            presented for review. Full rollback available for 30 days.

ABUSE-K006: Prompt injection via Proposition content — adversarial text in Proposition
            content designed to manipulate AI Agent reasoning
  Given:    ACT-K001 or ACT-K006 creates Proposition with adversarial content
  When:     AI Agent (ACT-K004/K005) processes that Proposition
  Then:     Agent Envelope constrains possible actions regardless of content.
            Agent output validated against schema before persistence.
            Proposition content treated as untrusted data by inference engine.
```

### Privacy Constraints

```
PRIV-K001: Data minimization — Proposition and Evidence schemas SHOULD mark Attributes
           as personal_data where applicable. Collection requires stated purpose.
PRIV-K002: Access logging — all reads of CLASS-K001 (PII) data generate audit Events.
PRIV-K003: Right to erasure — PII Attributes cryptographically shredded (encryption
           key destroyed). Provenance chain structure retained (who/when is erased,
           but the fact that a Proposition exists and its non-PII content persist
           for epistemic integrity). Shredded fields replaced with
           "[REDACTED — right to erasure exercised, {date}]".
PRIV-K004: Data portability — CAP-K024 / IFC-K012. Actor may export all Propositions
           they authored, all Evidence they submitted, and all metadata in
           machine-readable format.
```

### Compliance

Applicable regulations determined by Organization's jurisdictions and knowledge Domain sensitivities. Known applicable frameworks: GDPR (right to erasure, data portability, purpose limitation), CCPA/CPRA, HIPAA (when Domain includes protected health information), EU AI Act (transparency for AI-generated content — INV-K007 addresses this), PIPL (China), DPDPA (India), LGPD (Brazil). Research-specific: Common Rule (human subjects), FAIR principles (findable, accessible, interoperable, reusable data). Classification-specific: national security classification frameworks where applicable. — Source: SRC-K013 (via SUBSTRATE SRC-013 equivalent)

---


### Threat Model

```
THREAT-K001: Epistemic poisoning — adversarial injection of false Propositions with
             fabricated Provenance
             — Mitigation: mandatory Source identification, confidence ceilings for
               unverified Sources, Calibration tracking, anomaly detection on
               Proposition creation patterns

THREAT-K002: Provenance laundering — making a low-trust claim appear high-trust by
             routing through multiple intermediate Sources
             — Mitigation: full provenance chain traversal. Confidence ceiling applies
               based on weakest link in chain, not most recent Source.

THREAT-K003: Confidence manipulation — AI agent systematically nudging Confidences in
             a direction via many small sub-threshold updates
             — Mitigation: cumulative confidence change tracking per Agent per time
               window. Alert when cumulative change exceeds threshold even if no
               single change does.

THREAT-K004: Contradiction suppression — Actor resolves Contradictions by deleting the
             inconvenient side rather than engaging with it
             — Mitigation: Contradictions cannot be deleted, only resolved with
               recorded rationale. Both sides preserved. Auditor access to all
               Contradiction resolutions.

THREAT-K005: Ontology corruption — malicious changes to an Ontology that cascade
             incorrect re-tagging across thousands of Propositions
             — Mitigation: Ontology changes require ACT-K003. Versioned with rollback.
               Propagation is reviewable before commitment (dry-run mode).

THREAT-K006: Cross-org knowledge exfiltration via shared Ontology alignment
             — Mitigation: Ontology structures are shareable; Proposition content is not
               shared without explicit per-Proposition or per-Domain permission grants.
```

### Encryption

- In transit: TLS 1.3+ for all communication. No exceptions.
- At rest: all persistent data encrypted. Encryption keys per Organization.
- Field-level: Propositions classified as sensitive (configured per Domain) encrypted
  at field level with Organization-specific keys.
- Provenance chains: integrity-protected via hash chaining. Cryptographic shredding
  for right-to-erasure compliance on personal knowledge.


---

## 11. BEHAVIORAL CONTRACTS (SYSTEM LAW)

### 11.1 Invariants (must ALWAYS hold)

```
INV-K001: Every Proposition MUST have non-empty Provenance at all times. There are no
          anonymous claims in the system.
          — Source: ASM-K004

INV-K002: Every Confidence value MUST be in [0, 1] with lower_bound ≤ value ≤ upper_bound.
          — Source: ASM-K003

INV-K003: Every mutation to every knowledge artifact MUST produce an immutable Revision
          Event BEFORE the mutation is visible to any Actor. The Revision log is the
          source of truth; current state is a materialized view.
          — Source: ASM-K008

INV-K004: The Dependency Graph MUST be acyclic. Any operation that would introduce a
          cycle MUST be rejected, and the detected cycle surfaced as a circular-reasoning
          Contradiction.
          — Source: TERM-K008

INV-K005: Contradictions MUST NOT be silently resolved. A Contradiction persists as a
          first-class object until explicitly resolved by an Actor with rationale.
          The only exception: automatic dissolution when a Context change makes the
          conflict inapplicable.
          — Source: ASM-K005

INV-K006: No AI Agent may perform any epistemic operation outside its Epistemic Envelope.
          Enforced at permission layer. No exceptions.
          — Source: ASM-K006

INV-K007: Machine-generated Propositions MUST carry immutable `authored_by_ai: true`
          metadata. This field cannot be set to false after creation, by any Actor,
          under any circumstances.
          — Source: ASM-K006, UNK-K005

INV-K008: No Proposition may be permanently deleted. Retracted Propositions are marked
          as retracted with rationale and superseding reference. Historical confidence
          states remain queryable.
          — Source: ASM-K001

INV-K009: Evidence is immutable once Active. New interpretations of existing Evidence
          are new Inferences, not modifications of the Evidence.
          — Source: CAP-K009

INV-K010: The Revision log is hash-chained per knowledge artifact. Each Revision includes
          the hash of the preceding Revision for the same artifact.
          — Source: ASM-K008

INV-K011: Organization ID is part of every knowledge artifact's identity path.
          Cross-Organization query returns empty set for non-shared artifacts.
          — Source: CAP-K025

INV-K012: Every Argument MUST have non-empty known_weaknesses. The system does not
          permit claims of perfection in reasoning.
          — Source: ASM-K002
```

### 11.2 Forbidden States

```
FORBID-K001: A Proposition with empty Provenance in any non-Draft status.
FORBID-K002: A Confidence value outside [0, 1] or with lower_bound > upper_bound.
FORBID-K003: A knowledge artifact with no associated Revision Events (orphaned from audit trail).
FORBID-K004: An AI Agent operating with a deactivated (kill_switch=true) or Revoked Envelope.
FORBID-K005: A cycle in the Dependency Graph.
FORBID-K006: A Contradiction with resolution_status = "resolved" and no resolution record.
FORBID-K007: A permanently deleted Proposition, Evidence, or Argument.
FORBID-K008: An Inference with no inspectable Method.
FORBID-K009: A Revision log with a broken hash chain.
FORBID-K010: A machine-generated Proposition with authored_by_ai = false.
FORBID-K011: Cross-Organization knowledge access without explicit, active permission grant.
FORBID-K012: An Argument with empty known_weaknesses.
```

### 11.3 Failure Guarantees

```
FAIL-K001: If Contradiction Detection fails during Proposition creation (FLOW-K001 step 7),
           the Proposition MUST still be created. Contradiction detection failure is logged
           and retried. The Proposition is NOT blocked by detection failure.
           — Rationale: It is better to have knowledge without contradiction analysis than
             to block knowledge entry. Contradictions will be detected on retry or
             future queries.

FAIL-K002: If Confidence propagation exceeds configured bounds (FLOW-K002 step 7c),
           the system MUST complete propagation for the bounded set and flag the remainder
           for human review. It MUST NOT silently stop propagation.

FAIL-K003: If the Computation Backend (DEP-K004) is unavailable, simple expression
           evaluation continues in-system. Complex inferences queue. The system MUST
           NOT block Proposition creation or Evidence submission due to inference
           backend failure.

FAIL-K004: If a notification or automation side effect fails during a knowledge flow,
           the triggering operation (Proposition creation, Confidence update, etc.)
           MUST NOT be rolled back. Side effect failure is logged and retried independently.

FAIL-K005: If Revision log integrity check detects a broken hash chain, the system MUST
           halt writes to the affected artifact's Revision log and alert ACT-K003 and
           ACT-K007. It MUST NOT continue appending to a corrupted chain.

FAIL-K006: If an AI Agent's kill switch activates during an in-progress epistemic operation,
           the system MUST cancel the operation if possible and MUST NOT begin any new
           operations for that Agent. Already-committed Revisions are not reversed.
```

---


### 11.2 Preconditions

```
PRE-K001: FLOW-K001 (Create Proposition) requires non-empty Provenance AND non-empty
          Context AND valid Confidence value.
          — Source: INV-K001, INV-K002

PRE-K002: FLOW-K002 (Update Confidence) requires the new Confidence value to differ from
          the current value. No-op updates are rejected (to prevent audit log noise).
          — Source: ASM-K008

PRE-K003: FLOW-K003 (Detect Contradiction) requires at least one configured detection
          Method for the Proposition's Domain.
          — Source: SRC-K004

PRE-K004: FLOW-K004 (Build Argument) requires all premises to exist and be accessible
          to the Actor, all Inferences in the chain to have valid Methods, and
          known_weaknesses to be non-empty.
          — Source: INV-K012

PRE-K005: FLOW-K005 (Inquiry Cycle) requires the Question to reference at least one
          valid Domain with configured quality thresholds.
          — Source: SRC-K001

PRE-K006: FLOW-K006 (Ontology Propagation) requires both old and new Ontology versions
          to exist and the diff to be computable.
          — Source: SRC-K006

PRE-K007: FLOW-K007 (Approval Routing) requires the AI Agent's Epistemic Envelope to
          have a designated, active human_approver.
          — Source: ASM-K006

PRE-K008: IFC-K012 (Data Export) requires ACT-K003 Role.
          — Source: NG-K003

PRE-K009: Contradiction resolution (IFC-K004 resolve) requires rationale to be non-empty
          AND Actor to have write permission on ALL conflicting Propositions (or be Steward).
          — Source: INV-K005
```

### 11.3 Postconditions

```
POST-K001: After FLOW-K001 (Create Proposition), a Revision Event with type=created
           exists and the Proposition is queryable by any Actor with read permission.
           Contradiction detection has run (or is queued if detection backend busy).
           — Source: INV-K003, CAP-K006

POST-K002: After FLOW-K002 (Update Confidence), a Revision Event exists recording
           old_confidence, new_confidence, trigger, and rationale. Propagation to
           dependent Propositions has been initiated (synchronous for ≤configured
           threshold, async for larger cascades).
           — Source: INV-K003, CAP-K012

POST-K003: After FLOW-K003 (Detect Contradiction), if conflicts found: Contradiction
           entities exist with status=unresolved, linked to all conflicting Propositions.
           Notifications sent to Proposition authors and Domain Stewards.
           — Source: INV-K005

POST-K004: After FLOW-K004 (Build Argument), the Argument exists with assessed strength.
           Conclusion Proposition is linked. Counter-arguments (if any) are linked.
           Creation Event recorded.
           — Source: INV-K012

POST-K005: After FLOW-K006 (Ontology Propagation), all affected Propositions are
           re-tagged according to migration rules. Migration report available. No
           Proposition is left with zero tags (minimum: flagged for human review).
           — Source: CAP-K016

POST-K006: After FLOW-K007 (Approval Routing), the approval decision is recorded.
           If approved: original action executed with dual attribution (agent + approver).
           If rejected: rejection Event recorded, agent notified.
           — Source: CAP-K022

POST-K007: After IFC-K012 (Data Export), the export file contains ALL knowledge
           artifacts within the requested scope. No Proposition within scope is omitted.
           PII fields are included only if Actor has CLASS-K001 access.
           — Source: CAP-K024
```

---


---

## 12. DECISION POINTS & JUDGMENT

```
DEC-K001: Contradiction Resolution Strategy — Context: FLOW-K003
  Inputs:          Conflicting Propositions, their Evidence, their Confidences
  Options:         (a) Accept one, retract other(s) (b) Revise both (c) Add Context
                   refinement that dissolves the conflict (d) Acknowledge disagreement
                   (e) Flag for further investigation
  Selection rule:
    NOT AUTOMATED. The system surfaces the Contradiction with all relevant Evidence.
    Resolution requires Actor intervention. The system MAY suggest options ranked by
    evidential support, but MUST NOT auto-resolve.
  Fallback:        If no Actor resolves within configured period: Contradiction persists
                   as "unresolved." This is an acceptable steady state.
  Audit:           Resolution record: which Propositions affected, method used, Actor,
                   rationale. Minority positions preserved.

DEC-K002: Confidence Propagation Priority — Context: FLOW-K002
  Inputs:          A Proposition whose confidence changed; the full set of dependent
                   Propositions (potentially large)
  Options:         (a) Breadth-first propagation (b) Depth-first (c) Priority-ordered
                   by dependency strength (d) Bounded propagation with cutoff
  Selection rule:
    CONFIGURABLE per Organization. Default: priority-ordered by dependency strength,
    with strongest dependencies propagated first. Bounded at configurable depth and
    breadth. Rationale: strongest dependencies are most likely to produce meaningful
    confidence changes in dependents.
  Fallback:        If propagation exceeds bounds: stop, flag remainder, notify stewards.
  Audit:           Propagation report: which Propositions updated, which flagged, depth
                   reached, total affected.

DEC-K003: Cross-Ontology Concept Alignment — Context: FLOW-K006, CAP-K017
  Inputs:          Concept from Ontology A, candidate equivalent in Ontology B
  Options:         (a) exact match (b) broader (c) narrower (d) related (e) no match
  Selection rule:
    SEMI-AUTOMATED. System computes similarity using configured methods (definitional
    similarity, structural similarity in ontology graph, usage similarity across
    Propositions). Suggests alignment with confidence. Human steward confirms or
    corrects. AI agent MAY suggest within Envelope constraints.
  Fallback:        If confidence below threshold: flag as "alignment_uncertain."
  Audit:           Alignment record: method used, confidence, human confirmation status.

DEC-K004: Source Trust Level Assessment — Context: ENT-K020, CAP-K027
  Inputs:          Source's Calibration history, domain, known biases
  Options:         (a) verified (b) provisional (c) unverified (d) blacklisted
  Selection rule:
    CONFIGURABLE per Organization with defaults:
    - verified: Calibration score above domain threshold for ≥3 measurement periods
    - provisional: some Calibration data but insufficient history
    - unverified: no Calibration data
    - blacklisted: Calibration score below minimum OR manual blacklist by ACT-K003
  Fallback:        New Sources default to "unverified." Their Propositions carry
                   confidence ceiling (configurable, default: 0.5).
  Audit:           Trust level changes logged as Revision events with rationale.
```

---


---

## 13. CONCURRENCY & ORDERING

```
CONC-K001: Concurrent Proposition modification
  Scenario:    Two Actors update Confidence on the same Proposition simultaneously
  Resolution:  Optimistic locking via ETag/If-Match header. Second write receives
               ERR-K015 (conflict). Actor must re-read and retry.
  — Source: ASM-K008

CONC-K002: Concurrent Contradiction resolution
  Scenario:    Two Actors resolve the same Contradiction simultaneously
  Resolution:  First-write-wins. Second Actor receives ERR-K015.
               Contradiction resolution is atomic.
  — Source: INV-K005

CONC-K003: Confidence propagation during concurrent updates
  Scenario:    Proposition B depends on A. A's confidence is updated. While propagation
               to B is in progress, another Actor directly updates B's confidence.
  Resolution:  Both updates applied in Event order. Propagation creates a Revision
               Event; direct update creates another. Final confidence reflects latest
               Revision. No propagation result is silently overwritten — both appear
               in Revision log.
  — Source: ASM-K008, CAP-K012

CONC-K004: Concurrent Ontology publication
  Scenario:    Two Stewards publish new versions of the same Ontology simultaneously
  Resolution:  Version numbers are server-assigned (monotonic). Second publish gets
               next version. Both versions exist. Propagation runs for whichever
               version is designated as "active" by Steward.
  — Source: SRC-K006

CONC-K005: Dependency creation during cycle check
  Scenario:    Two Dependencies created simultaneously that together form a cycle
               (A→B and B→A submitted concurrently)
  Resolution:  Serialized cycle check per Dependency Graph partition. Second dependency
               fails cycle check. ERR-K005 returned.
  — Source: INV-K004
```

### Race Conditions to Prevent

```
RACE-K001: Double contradiction detection
  Scenario:    Same Contradiction detected by two concurrent FLOW-K003 executions
  Prevention:  Contradiction deduplication: before creating ENT-K009, check for existing
               Contradiction with same proposition set. If exists, skip creation.
               Dedup check + create is atomic.
  — Source: FLOW-K003

RACE-K002: Proposition retraction during confidence propagation
  Scenario:    Proposition A retracted while propagation from A to dependents is in progress
  Prevention:  Propagation checks target Proposition status at each hop. If source
               Proposition is Retracted, propagation continues (dependents need to know
               their foundation was retracted) but the propagated confidence change
               reflects the retraction.
  — Source: FLOW-K002, SM-K001

RACE-K003: Envelope kill switch during in-progress inference
  Scenario:    AI Agent is mid-operation when kill switch activated
  Prevention:  Kill switch check at every step boundary in FLOW-K001/K002/K004.
               If kill_switch=true at any check: cancel remaining steps, record
               partial completion status. Already-committed Revisions not reversed.
  — Source: FAIL-K006, SM-K006

RACE-K004: Export during active propagation
  Scenario:    Bulk export initiated while confidence propagation cascade is active
  Prevention:  Export captures snapshot at initiation time (using Event sequence
               number as watermark). Propagation events after watermark not included.
               Export metadata records watermark for consumer awareness.
  — Source: IFC-K012

RACE-K005: Offline sync conflict
  Scenario:    Edge node creates Proposition offline. Server creates conflicting
               Proposition (same content, different confidence) before sync.
  Prevention:  Offline sync per SUBSTRATE pattern (DEC-001 equivalent): configurable
               per Organization. Default: fork (both versions retained, linked by
               "sync_conflict" Relation, Actor must resolve).
  — Source: CAP-K026
```

### Ordering Guarantees

```
ORD-K001: Revision Events per artifact: strictly ordered by server-assigned sequence
          number. Concurrent writers serialized at commit.
ORD-K002: Confidence propagation: happens-before ordering within a single cascade.
          Independent cascades (from different root changes) may interleave.
ORD-K003: Cross-artifact queries: eventual consistency, ≤2s staleness budget.
          Single-artifact reads: strongly consistent.
ORD-K004: Event stream (IFC-K011): ordered per Organization partition. Cross-org
          ordering not guaranteed.
```

### Idempotency

```
IDEMP-K001: All POST operations on IFC-K001 through IFC-K010: idempotent via
            Idempotency-Key header (UUID). Key valid for 30-day window within
            Organization scope.
IDEMP-K002: Confidence propagation hops: idempotent per (source_revision_id,
            target_proposition_id) pair. Duplicate propagation for same trigger
            is no-op.
IDEMP-K003: Contradiction detection: idempotent per proposition-pair. Re-running
            detection on same pair with no state change produces no new Contradiction.
```

### Atomicity Boundaries

```
ATOM-K001: Single Proposition creation (FLOW-K001 steps 1–9): atomic.
           Contradiction detection (step 7): included in atomic boundary.
           Notifications (step 10): async, NOT atomic with creation.
ATOM-K002: Single Confidence update (FLOW-K002 steps 1–5): atomic.
           Propagation (steps 6–8): each hop is independently atomic.
ATOM-K003: Argument creation (FLOW-K004): atomic.
ATOM-K004: Contradiction resolution: atomic (resolution record + status change).
ATOM-K005: Ontology propagation (FLOW-K006): per-Concept migration is atomic.
           Full Ontology migration is eventually consistent.
```

---


---

## 14. ERROR HANDLING & RECOVERY

### 14.1 Error Taxonomy

```
ERR-K001: Missing provenance — Proposition or Evidence submitted without Source/creator
          HTTP: 422. Detail: field path. — Source: INV-K001
ERR-K002: Missing context — Proposition submitted without Context
          HTTP: 422. Detail: field path. — Source: CAP-K001
ERR-K003: Epistemic Envelope violation — AI Agent attempted operation outside Envelope
          HTTP: 403. Detail: which constraint violated (domain, operation, threshold).
          — Source: INV-K006
ERR-K004: Invalid confidence — Confidence value outside [0,1] or bounds violated
          HTTP: 422. Detail: field, value, constraint. — Source: INV-K002
ERR-K005: Dependency cycle detected — Operation would create circular reasoning
          HTTP: 409. Detail: cycle path [Proposition IDs]. — Source: INV-K004
ERR-K006: Broken inference chain — Argument's inference steps don't connect premises
          to conclusion
          HTTP: 422. Detail: gap location in chain. — Source: IFC-K007
ERR-K007: Missing weakness acknowledgment — Argument submitted with empty known_weaknesses
          HTTP: 422. Detail: "known_weaknesses must be non-empty". — Source: INV-K012
ERR-K008: Immutable content modification — Attempt to modify Active Evidence or
          committed Revision
          HTTP: 409. Detail: entity ID, immutability reason. — Source: INV-K009
ERR-K009: Missing rationale — Contradiction resolution, retraction, or other
          consequential action attempted without rationale text
          HTTP: 422. Detail: "rationale is required for this operation". — Source: INV-K005
ERR-K010: Authorization error — Actor lacks permission for requested operation
          HTTP: 403. Detail: required permission, Actor's current grants.
          — Source: Section 9
ERR-K011: Entity not found — Referenced Proposition, Evidence, etc. does not exist
          or is not in Actor's scope
          HTTP: 404. No detail (to avoid information leakage per INV-K011).
ERR-K012: Query timeout — Query or computation exceeded time budget
          HTTP: 504. Detail: "query exceeded {n}s budget. Try narrower scope."
          — Source: Section 14, IFC-K005
ERR-K013: Query too broad — Query would scan more than configured maximum
          HTTP: 422. Detail: estimated result count, maximum allowed.
ERR-K014: Axiom unsatisfiable — Ontology axiom set is contradictory
          HTTP: 422. Detail: conflicting axioms. — Source: IFC-K006
ERR-K015: Optimistic lock conflict — Entity modified since last read
          HTTP: 409. Detail: entity ID, current ETag.
          — Source: CONC-K001
ERR-K016: Insufficient hypotheses — Experiment references fewer than 2 Hypotheses
          HTTP: 422. Detail: "Experiments must test ≥2 Hypotheses."
          — Source: ENT-K018
ERR-K017: Insufficient calibration sample — Calibration submitted with sample_size
          below configured minimum
          HTTP: 422. Detail: minimum required, actual provided. — Source: ENT-K021
ERR-K018: Approval expired — Approval request past timeout (default 72h)
          HTTP: 410 (Gone). Detail: expiry time. — Source: FLOW-K007
ERR-K019: Rate limited — Actor exceeded configured operation rate
          HTTP: 429. Headers: Retry-After, X-RateLimit-Remaining.
ERR-K020: Internal error — Unexpected system failure
          HTTP: 500. Detail: correlation ID only. No stack traces. No internal state.
```

All errors use RFC 7807 Problem Details format:
```json
{
  "type": "urn:substrate-knowledge:error:ERR-K###",
  "title": "Human-readable title",
  "status": 4xx/5xx,
  "detail": "Specific detail for this instance",
  "instance": "/orgs/{org}/propositions/{id}"
}
```

### 14.2 Semantics

**User-facing errors:** All errors return structured RFC 7807 responses. No stack traces, no internal identifiers beyond correlation ID, no database schema details. Error `type` URIs are stable and documented.

**Retry semantics:**
- ERR-K015 (conflict): automatic re-read + re-validate if Actor permits. Otherwise surface.
- ERR-K012 (timeout): suggest narrower scope.
- ERR-K019 (rate limit): retry after Retry-After header value.
- ERR-K020 (internal): retry with exponential backoff, max 3 attempts.
- All others: not automatically retried.

**Partial failure:** FLOW-K001/K002 notification side effects (step 10/step 8+) may fail while the triggering operation succeeds. The operation is NOT rolled back. Side effect failure is logged as separate Event and retried via background reconciliation (3 retries, 1m/5m/30m — per FAIL-K004).

**Degraded mode:**
- DEP-K002 down: new authentications blocked. Existing sessions valid until expiry.
- DEP-K003 down: new Source registration blocked. Existing Sources unaffected. Unverified Sources accepted with confidence floor.
- DEP-K004 down: simple expression evaluation continues. Complex inferences queue. Proposition CRUD unaffected.
- DEP-K005 down: notifications queue with 72h TTL. All other operations continue.
- DEP-K006 down: Evidence metadata accessible. Content unavailable. All other operations continue.
- DEP-K007 down: Knowledge operations continue. Cross-SUBSTRATE references unresolvable. Queued for retry.

**Recovery:**
- After DEP-K004 recovery: queued inferences execute in submission order. Results may differ from real-time execution (stale inputs); all results timestamped with computation time.
- After prolonged offline (CAP-K026): sync per RACE-K005. Conflicts surfaced.
- After FAIL-K005 (hash chain break): writes halted on affected artifact. Manual investigation. ACT-K003 and ACT-K007 notified.

**Circuit breakers:**
- INT-K001 (Source Registry): open after 5 failures in 60s. Half-open at 120s.
- INT-K002 (Computation): open after 3 failures in 120s. Half-open at 300s.
- INT-K003 (Content Store): open after 5 failures in 120s. Half-open at 60s.
- INT-K004 (Communication): open after 10 failures in 120s. Half-open at 60s.
- INT-K005 (SUBSTRATE): open after 5 failures in 60s. Half-open at 60s.
- INT-K006 (Identity): open after 5 failures in 60s. Half-open at 60s.

---


---

## 15. PERSISTENCE REQUIREMENTS (LOGICAL)

```
PERS-K001: Propositions — Source: ASM-K010
  Access patterns:       Read-heavy (20:1 read:write). Queries by: ID, Domain, Context,
                         Confidence range, Concept tags, Source, timestamp, status.
  Consistency:           Strong for single-Proposition reads. Eventual (≤2s) for cross-
                         Proposition queries and Dependency Graph traversals.
  Retention:             Never deleted. Retracted Propositions retained with status.
  Size projections:      ~20B propositions (all organizations globally). ~4KB average.
                         ~80TB total. Growth: ~2B/year.

PERS-K002: Revision Log — Source: ASM-K008
  Access patterns:       Write per knowledge mutation. Read for audit, time-travel.
  Consistency:           Strong (append-only, hash-chained per artifact).
  Retention:             Never deleted. Indefinite.
  Size projections:      ~200B revisions. ~1KB average. ~200TB. Growth: ~20B/year.

PERS-K003: Dependency Graph — Source: TERM-K008
  Access patterns:       Read on every confidence propagation. Write on Proposition
                         creation and Inference creation.
  Consistency:           Strong (cycle detection on every write).
  Size projections:      ~100B edges. ~200 bytes average. ~20TB.

PERS-K004: Evidence — Source: SRC-K001
  Access patterns:       Write-once, read-many. Metadata queried frequently.
                         Full content retrieved on demand.
  Consistency:           Metadata: strong. Content: eventual (DEP-K006).
  Size projections:      ~5B evidence artifacts. Metadata: ~2KB avg.
                         Content: ~500KB avg. Total content: ~2.5EB.

PERS-K005: Ontologies — Source: SRC-K006
  Access patterns:       Read-heavy. Write: infrequent (version changes).
  Size projections:      ~1M ontologies, ~50M concepts, ~200M relations.
                         ~10GB total. Low growth.
```

---


---

## 16. MIGRATION & ONBOARDING

### Data Migration

This is NOT greenfield at the knowledge layer. SUBSTRATE-KNOWLEDGE replaces ~120,000 existing knowledge products.

- **Source systems:** Every knowledge management, reference management, decision support, and evidence synthesis product in SRC-K001 through SRC-K011.
- **Mapping:** ASI-1 has computed the mapping from every schema in every product:
  - `pubmed.Article` → ENT-K001 (Proposition) + ENT-K002 (Evidence) + ENT-K004 (Provenance)
  - `zotero.Item` → ENT-K020 (Source) + ENT-K004 (Provenance) + ENT-K002 (Evidence)
  - `confluence.Page` → ENT-K001 (Proposition) + ENT-K010 (Revision history) + ENT-K026 (Annotations)
  - `mesh.Descriptor` → ENT-K011 (Concept) in ENT-K013 (MeSH Ontology)
  - `cochrane.Review` → ENT-K015 (Argument) + ENT-K018 (Experiments) + ENT-K003 (Confidence grades)
  - `palantir.Assessment` → ENT-K001 (Proposition) + ENT-K003 (Confidence) + ENT-K020 (Source with Calibration)
  - `wikidata.Item` → ENT-K011 (Concept) + ENT-K012 (Relations) + ENT-K004 (Provenance)
- **Transformation rules:** Product-specific adaptors convert source data into SUBSTRATE-KNOWLEDGE Events. Revision log populated as if Organization had used SUBSTRATE-KNOWLEDGE from inception.
- **Migration strategy:** Incremental (dual-write). Source system continues operating. SUBSTRATE-KNOWLEDGE receives shadow writes. When parity confirmed: cutover.
- **Rollback plan:** Source system remains active during dual-write. Cutover reversible until source system explicitly decommissioned (ACT-K003 decision).

### Cutover Plan

- Old and new systems run simultaneously during dual-write phase.
- "Migration complete" signal: ≥30 days of dual-write with zero knowledge discrepancies, confirmed by ACT-K007 (Auditor).

### Onboarding Flow (new Organization, no migration)

1. ACT-K003 creates Organization with jurisdictions and locale.
2. System suggests applicable Domain templates and Ontologies based on industry.
3. ACT-K003 selects and customizes templates → generates Configuration.
4. Configuration applied → Domain definitions, Ontologies, Methods, quality thresholds created.
5. ACT-K003 invites Actors and assigns Roles.
6. System immediately operational. No seed data required beyond Ontology structure.

---


---

## 17. OPERATIONAL PROFILE

### 17.1 Performance & Resource Constraints

```
- Proposition CRUD: p50 ≤100ms, p95 ≤300ms, p99 ≤1s
- Confidence update (single): p50 ≤100ms, p95 ≤300ms, p99 ≤1s
- Confidence propagation (per hop): p50 ≤200ms, p95 ≤500ms, p99 ≤2s
- Contradiction detection (per pair): p50 ≤500ms, p95 ≤2s, p99 ≤5s
- Dependency Graph cycle check: p50 ≤50ms, p95 ≤200ms, p99 ≤1s
- Query/View: ≤2s for ≤1M Propositions, ≤10s for ≤100M Propositions
- Ontology traversal: ≤500ms for ≤100K Concepts
- Throughput: 10B write events/day peak (ASM-K011). ~115K events/second sustained.
- Payload limits: Proposition ≤4KB. Evidence metadata ≤10KB. Evidence content ≤5GB.
- Rate limits: Default 500 ops/min per Actor. Per Organization, per Role, per Envelope.
```

---


### 17.2 Configuration & Environment

**Environment variables:** Implementation-defined. Spec does not constrain.

**Feature flags:**
```
- offline_mode_enabled — Purpose: enable/disable CAP-K026. Default: true. Toggle: ACT-K003.
- agent_general_enabled — Purpose: allow ACT-K005 (general AI agents). Default: false. Toggle: ACT-K003.
- cross_org_sharing_enabled — Purpose: enable cross-Organization knowledge sharing. Default: false. Toggle: ACT-K003.
- auto_contradiction_detection — Purpose: run FLOW-K003 automatically on Proposition creation. Default: true. Toggle: ACT-K003.
- propagation_enabled — Purpose: enable automatic confidence propagation (FLOW-K002 steps 6-8). Default: true. Toggle: ACT-K003. When false, propagation events are queued but not executed.
```

**Secrets:** All secrets (API keys, encryption keys, Identity provider credentials) stored in HSM or equivalent. Rotation: API keys every 90 days. Encryption keys every 365 days. Session signing keys every 30 days.

**External endpoints:** DEP-K001 through DEP-K007 — all environment-specific.

### 17.3 Versioning & Evolution

- **API versioning:** URL path prefix: `/v1/orgs/...`. Major version in path. Minor/patch changes are backward-compatible additions.
- **Backward compatibility rules:** New optional fields on request/response schemas are non-breaking. New enum values on response schemas are non-breaking. Removal or renaming of any field is breaking. New required request fields are breaking.
- **Breaking change policy:** 12-month deprecation period. Deprecated endpoints return `Sunset` header with removal date. Both old and new versions served simultaneously during deprecation.
- **Schema evolution:** Ontology versions are immutable once published. New versions created for changes. Propositions retain reference to the Ontology version under which they were created. Migration to new Ontology version is explicit (FLOW-K006).
- **Event schema:** Append-only. New Event types may be added. Existing types never modified. Consumers must ignore unknown fields (forward-compatible).

### 17.4 Storage & Infrastructure Recommendations (NON-BINDING)

```
REC-K001: Revision log persistence — Append-only, partitioned log (Kafka-like or purpose-
          built event store). Partition by Organization ID.
          — Tradeoffs: High write throughput. Cross-org queries more expensive.
          — Source: ASM-K008

REC-K002: Proposition materialized state — Document store or wide-column store with
          Organization + Domain + Proposition ID as composite key.
          — Tradeoffs: Fast point reads. Complex graph traversals require pre-computed
            adjacency lists or separate graph index.
          — Source: ASM-K010

REC-K003: Dependency Graph — Graph database or adjacency list with cycle detection
          at write time.
          — Tradeoffs: Graph DB gives fast traversal for propagation. Relational store
            with recursive CTE is simpler but slower at depth >5.
          — Source: TERM-K008, INV-K004

REC-K004: Content Store — Content-addressable storage with deduplication.
          — Tradeoffs: Dedup saves ~60% for academic content (many papers cite same figures).
          — Source: SRC-K001

REC-K005: Contradiction detection — Pre-computed pairwise consistency index per Domain.
          Updated incrementally on Proposition creation.
          — Tradeoffs: Space: O(n²) per Domain. Amortized detection time: O(1) per new
            Proposition (check against index, not full scan). Rebuild cost: O(n²).
          — Source: FLOW-K003

REC-K006: Confidence propagation — Message queue per Dependency Graph partition.
          Bounded fan-out with priority ordering by dependency strength.
          — Tradeoffs: Async propagation introduces latency (seconds to minutes for deep
            cascades). Synchronous propagation blocks the triggering operation.
            Hybrid: synchronous for depth ≤3, async beyond.
          — Source: FLOW-K002, UNK-K002
```

---


---

## 18. EXECUTABLE SPECIFICATION OUTLINE (TEST PLAN)

### Contract Tests

```
TEST-K001: Provenance requirement — Covers: INV-K001, FORBID-K001
  Given:        A Proposition creation request with empty provenance
  When:         Proposition creation attempted
  Then:         ERR-K001 returned. Proposition NOT created.
  Failure means: System allows anonymous knowledge claims.

TEST-K002: Confidence bounds — Covers: INV-K002, FORBID-K002
  Given:        A Confidence assessment with value=0.8, lower_bound=0.9, upper_bound=0.7
  When:         Confidence assignment attempted
  Then:         ERR-K004 returned. Confidence NOT assigned.
  Failure means: System allows incoherent uncertainty representation.

TEST-K003: Dependency cycle detection — Covers: INV-K004, FORBID-K005
  Given:        Proposition A depends on B, B depends on C
  When:         Dependency C → A creation attempted
  Then:         ERR-K005 returned. Dependency NOT created. Circular-reasoning
                Contradiction surfaced with the three propositions.
  Failure means: System allows circular reasoning without detection.

TEST-K004: Contradiction persistence — Covers: INV-K005, FORBID-K006
  Given:        Contradiction between Propositions A and B, status = "unresolved"
  When:         Actor attempts to delete the Contradiction
  Then:         Deletion rejected. Contradiction persists.
  When:         Actor attempts to resolve without providing rationale
  Then:         Resolution rejected.
  When:         Actor resolves with rationale
  Then:         Contradiction status = resolved. Both Propositions still exist.
                Resolution record includes rationale and Actor.
  Failure means: System allows silent contradiction suppression.

TEST-K005: AI authorship immutability — Covers: INV-K007, FORBID-K010
  Given:        Proposition created by AI Agent with authored_by_ai = true
  When:         Any Actor (including admin) attempts to set authored_by_ai = false
  Then:         Modification rejected. Field remains true.
  Failure means: Machine-generated knowledge can masquerade as human-authored.

TEST-K006: Revision event generation — Covers: INV-K003, FORBID-K003
  Given:        Proposition with confidence = 0.7
  When:         Confidence updated to 0.4
  Then:         Revision Event exists with: old_confidence=0.7, new_confidence=0.4,
                trigger, actor, rationale. Hash chain intact.
  Failure means: Knowledge can change without audit trail.

TEST-K007: No permanent deletion — Covers: INV-K008, FORBID-K007
  Given:        Published Proposition with confidence = 0.9
  When:         Actor attempts permanent deletion
  Then:         Deletion rejected.
  When:         Actor retracts Proposition with rationale
  Then:         Proposition status = Retracted. Still queryable. Confidence history
                preserved. Retraction reason recorded.
  Failure means: Knowledge can be destroyed rather than corrected.

TEST-K008: Epistemic Envelope enforcement — Covers: INV-K006, FORBID-K004
  Given:        AI Agent with Epistemic Envelope: domain_scope = [Medicine],
                confidence_change_threshold = 0.1
  When:         Agent attempts to propose Proposition in Domain "Finance"
  Then:         ERR-K003 returned. Operation rejected.
  When:         Agent attempts confidence update of Δ0.3 in Domain "Medicine"
  Then:         Operation routed to human approval (FLOW-K007). Not directly applied.
  When:         Agent's kill_switch is set to true
  Then:         All pending operations cancelled. No new operations accepted.
  Failure means: AI agents can operate without bounds on knowledge.

TEST-K009: Evidence immutability — Covers: INV-K009
  Given:        Evidence artifact with status = Active
  When:         Actor attempts to modify content
  Then:         Modification rejected. Content unchanged.
  When:         Actor creates new Inference re-interpreting the Evidence
  Then:         New Inference accepted. Original Evidence unchanged. Both linked.
  Failure means: Raw evidence can be retroactively altered.

TEST-K010: Revision log integrity — Covers: INV-K010, FORBID-K009
  Given:        Proposition with 5 Revisions, hash chain intact
  When:         Attempt to modify Revision #3
  Then:         Modification rejected. Hash chain unchanged.
  When:         Integrity check run
  Then:         All hashes verify. No tampering detected.
  Failure means: Belief history can be rewritten.

TEST-K011: Confidence propagation — Covers: CAP-K012, FLOW-K002
  Given:        Proposition A (confidence 0.9) depends on Proposition B (confidence 0.8)
  When:         Proposition B's confidence updated to 0.3
  Then:         Proposition A's confidence is re-evaluated and a Revision Event recorded.
                The new confidence for A reflects the weakened foundation.
  Failure means: Beliefs remain confident despite their foundations crumbling.

TEST-K012: Contradiction detection on creation — Covers: CAP-K006, FLOW-K001
  Given:        Existing Proposition: "Water boils at 100°C at 1 atm"
                (Context: standard conditions, Domain: physics, confidence: 0.99)
  When:         New Proposition created: "Water boils at 80°C at 1 atm"
                (same Context and Domain)
  Then:         Contradiction detected and surfaced. Both Propositions exist.
                Contradiction status = "unresolved."
  Failure means: Conflicting claims coexist without any alert.

TEST-K013: Argument weakness requirement — Covers: INV-K012, FORBID-K012
  Given:        Argument creation request with known_weaknesses = []
  When:         Argument creation attempted
  Then:         ERR-K007 returned. Argument NOT created.
  Failure means: System allows claims of perfect reasoning.

TEST-K014: Cross-organization isolation — Covers: INV-K011, FORBID-K011
  Given:        Org A has Proposition P. Org B has no sharing agreement with Org A.
  When:         Actor in Org B queries for Proposition P
  Then:         Empty result set. No error (to avoid information leakage).
  Failure means: Knowledge leaks across organizational boundaries.

TEST-K015: Source confidence ceiling — Covers: DEC-K004, CAP-K010
  Given:        External System submits Proposition from unverified Source
  When:         Proposition created
  Then:         Confidence ceiling applied (default: 0.5 regardless of stated confidence).
                Source flagged as unverified. Provenance records external origin.
  Failure means: Unverified claims enter system at arbitrarily high confidence.

TEST-K016: Belief time-travel — Covers: CAP-K005
  Given:        Proposition with Revision history: 0.3 (Jan 1) → 0.7 (Feb 1) → 0.4 (Mar 1)
  When:         Actor queries confidence as of Jan 15
  Then:         Returns 0.3 (state after Jan 1 revision, before Feb 1 revision)
  Failure means: System cannot reconstruct past epistemic states.

TEST-K017: Cumulative AI confidence manipulation detection — Covers: THREAT-K003
  Given:        AI Agent with confidence_change_threshold = 0.1
                Agent makes 20 updates of Δ0.05 each to the same Proposition
  When:         Cumulative change reaches configured alert threshold (default: 0.3)
  Then:         Alert generated. Agent operations on this Proposition suspended pending
                human review.
  Failure means: AI can manipulate beliefs via salami-slicing under the per-update threshold.
```

---


---

## 19. OBSERVABILITY & AUDITABILITY

### Structured Logs

```
LOG-K001: proposition_created — Fields: { org_id, proposition_id, domain_ids, actor_id,
          actor_type, authored_by_ai, confidence_value, evidence_count, timestamp }
          Trigger: FLOW-K001 step 9

LOG-K002: confidence_updated — Fields: { org_id, proposition_id, actor_id, actor_type,
          old_confidence, new_confidence, trigger_type, trigger_ref, propagation_initiated }
          Trigger: FLOW-K002 step 9

LOG-K003: contradiction_detected — Fields: { org_id, contradiction_id, proposition_ids,
          type, severity, detection_method, timestamp }
          Trigger: FLOW-K003 step 3

LOG-K004: contradiction_resolved — Fields: { org_id, contradiction_id, resolution_method,
          actor_id, chosen_proposition_id, timestamp }
          Trigger: IFC-K004 resolve

LOG-K005: envelope_violation — Fields: { org_id, agent_id, envelope_id, operation_attempted,
          constraint_violated, timestamp }
          Trigger: ERR-K003

LOG-K006: envelope_kill_switch — Fields: { org_id, agent_id, envelope_id, trigger_reason,
          operations_cancelled, actor_id, timestamp }
          Trigger: SM-K006 Active → Suspended

LOG-K007: approval_routed — Fields: { org_id, agent_id, envelope_id, proposed_action,
          confidence_change_magnitude, approver_id, timestamp }
          Trigger: FLOW-K007 step 2

LOG-K008: approval_decided — Fields: { org_id, approval_id, decision: approved|rejected|
          expired, actor_id, timestamp }
          Trigger: FLOW-K007 steps 6/7/8

LOG-K009: propagation_bounded — Fields: { org_id, root_proposition_id, depth_reached,
          breadth_reached, propositions_updated, propositions_flagged, timestamp }
          Trigger: FLOW-K002 step 7c

LOG-K010: hash_chain_violation — Fields: { org_id, artifact_type, artifact_id,
          expected_hash, actual_hash, revision_sequence, timestamp }
          Trigger: FAIL-K005

LOG-K011: export_initiated — Fields: { org_id, actor_id, scope, format, timestamp }
          Trigger: IFC-K012

LOG-K012: source_trust_changed — Fields: { org_id, source_id, old_trust, new_trust,
          actor_id, rationale_hash, timestamp }
          Trigger: IFC-K009 trust update

LOG-K013: pii_access — Fields: { org_id, actor_id, entity_type, entity_id,
          fields_accessed, purpose, timestamp }
          Trigger: Any read of CLASS-K001 data
```

### Audit Trail

All state-changing operations are attributed to an Actor via the Revision Event log (INV-K003). Retention: indefinite (Revisions are never deleted — INV-K008, INV-K010). The Revision log IS the audit trail — no separate audit system is needed. Hash chain integrity (INV-K010) provides tamper evidence.

Time-travel queries (CAP-K005) enable full state reconstruction at any past timestamp.

### Metrics

```
MET-K001: propositions_created_total — Type: counter — Purpose: track knowledge creation rate
          Labels: org_id, domain_id, actor_type, authored_by_ai
MET-K002: confidence_updates_total — Type: counter — Purpose: track belief revision rate
          Labels: org_id, domain_id, actor_type, trigger_type
MET-K003: contradictions_active — Type: gauge — Purpose: track unresolved contradiction count
          Labels: org_id, domain_id, severity
MET-K004: propagation_depth — Type: histogram — Purpose: track cascade depth distribution
          Labels: org_id, domain_id
MET-K005: propagation_latency_seconds — Type: histogram — Purpose: track end-to-end
          propagation time
          Labels: org_id, depth_bucket
MET-K006: query_latency_seconds — Type: histogram — Purpose: track query performance
          Labels: org_id, depth (surface|deep), result_count_bucket
MET-K007: envelope_violations_total — Type: counter — Purpose: track AI boundary violations
          Labels: org_id, agent_id, constraint_type
MET-K008: approval_queue_depth — Type: gauge — Purpose: track pending human approvals
          Labels: org_id, approver_id
MET-K009: approval_latency_seconds — Type: histogram — Purpose: track time-to-decision
          Labels: org_id, decision_type
MET-K010: evidence_submissions_total — Type: counter — Purpose: track evidence inflow
          Labels: org_id, domain_id, source_trust_level
MET-K011: dependency_graph_edges — Type: gauge — Purpose: track graph size (capacity planning)
          Labels: org_id
MET-K012: revision_log_size_bytes — Type: gauge — Purpose: track storage growth
          Labels: org_id
```

### Tracing

Distributed tracing required for multi-step operations (FLOW-K002 propagation, FLOW-K005 inquiry cycle, FLOW-K006 ontology propagation). Format: W3C Trace Context (traceparent/tracestate headers). Each FLOW step is a span. Cross-service calls (INT-K001 through INT-K006) propagate trace context.

### Alerts

```
ALERT-K001: Hash chain integrity violation detected
            Severity: CRITICAL — Notify: ACT-K003, ACT-K007 — Source: FAIL-K005

ALERT-K002: AI Agent cumulative confidence drift exceeds threshold
            Severity: HIGH — Notify: Envelope human_approver, ACT-K003 — Source: THREAT-K003

ALERT-K003: Propagation bounds exceeded (cascade too large)
            Severity: MEDIUM — Notify: ACT-K003 — Source: FLOW-K002 step 7c

ALERT-K004: Contradiction resolution pattern anomaly (possible suppression)
            Severity: MEDIUM — Notify: ACT-K003 — Source: ABUSE-K004

ALERT-K005: Ontology propagation affecting >1000 Propositions
            Severity: HIGH — Notify: ACT-K003 (requires second approval) — Source: ABUSE-K005

ALERT-K006: Source trust level downgraded from verified to blacklisted
            Severity: HIGH — Notify: ACT-K003 — Source: DEC-K004
            Downstream: all Propositions from this Source flagged for re-evaluation.

ALERT-K007: Computation backend circuit breaker open
            Severity: MEDIUM — Notify: ACT-K003 — Source: INT-K002

ALERT-K008: Approval queue depth exceeds threshold (>50 pending per approver)
            Severity: MEDIUM — Notify: ACT-K003 — Source: MET-K008

ALERT-K009: Epistemic flooding detected (rate abuse)
            Severity: HIGH — Notify: ACT-K003 — Source: ABUSE-K001
```

### Incident Reconstruction

An incident can be fully reconstructed from Revision Event log + structured logs + metrics. The Revision Event log provides complete causal history (what changed, who, when, why, triggered by what). Structured logs provide system behavior context. Metrics provide aggregate patterns. No additional data is needed for epistemic incident reconstruction.

### PII in Telemetry

MUST redact: Actor names, email addresses, Source names (when type=human_agent). MUST NEVER appear in logs, metrics, or traces: personal knowledge content (CLASS-K001 field values), Proposition content classified as CLASS-K002, encryption keys, authentication tokens, session tokens. All telemetry uses Actor UUIDs and Entity UUIDs — never natural-language identifiers.

---


---

## 20. DEFINITION OF DONE

### 20.1 Build Complete (code is done)

- All ENT-K### entities implementable via API (IFC-K001 through IFC-K013)
- All FLOW-K### flows executable end-to-end
- All SM-K### state machines enforced
- All TEST-K### scenarios passing
- All INV-K### invariants enforced and tested
- All FORBID-K### states unreachable and tested
- Configuration schema (JSON Schema) exists and validates
- OpenAPI spec generated and validates
- Lint / type-check / static analysis clean
- API documentation generated from OpenAPI spec
- Runbook documenting degraded mode procedures

### 20.2 Ship Ready (safe to deploy)

- Logging configured for all LOG-K### events
- Alerting configured for all ALERT-K### conditions
- Monitoring dashboards for all MET-K### metrics
- Distributed tracing operational for multi-step flows
- Seed Ontologies loaded (at minimum: one Domain template per target industry)
- Circuit breakers configured for all INT-K### integrations
- Encryption at rest and in transit verified
- PII redaction in telemetry verified (no CLASS-K001 data in logs)
- Offline mode tested (CAP-K026)
- Rollback plan documented and tested
- Manual verification checklist:
  - [ ] Create Proposition → appears in query → Revision Event exists
  - [ ] Contradiction detection fires on conflicting Proposition
  - [ ] Confidence propagation reaches dependents
  - [ ] AI Agent stopped by Envelope boundary
  - [ ] Kill switch halts Agent immediately
  - [ ] Export produces complete, valid output
  - [ ] Time-travel query returns correct historical state

---


---

## 21. OPEN QUESTIONS & RISKS

```
OQ-K001: Optimal confidence propagation strategy at global scale
  Impact:               UNK-K002. Worst case: single revision triggers millions of updates.
                        Could cause propagation storms that overwhelm the system.
  Suggested resolution: Implement bounded propagation (configurable depth/breadth)
                        first. Measure real-world cascade depth distributions in
                        production. Adjust bounds based on empirical data.
  Owner:                ACT-K003 (per Organization policy) + platform engineering
  Deadline:             Before any Organization exceeds 10M Propositions

OQ-K002: Cross-cultural ontology alignment completeness
  Impact:               UNK-K003. Knowledge expressed in different linguistic and cultural
                        traditions may not have clean concept mappings.
  Suggested resolution: Accept partial alignment as a permanent state. Provide "alignment
                        gap" reporting. Invest in domain-specific alignment for highest-
                        priority language pairs first.
  Owner:                ACT-K003 (per Domain)
  Deadline:             UNKNOWN — ongoing research problem

OQ-K003: Legal status of machine-generated Propositions
  Impact:               UNK-K005. May affect admissibility in legal proceedings, regulatory
                        compliance, and intellectual property claims.
  Suggested resolution: INV-K007 (immutable AI authorship flag) provides the mechanism.
                        Legal interpretation is jurisdiction-dependent and evolving.
                        System is compliant by providing transparency; legal interpretation
                        is outside system scope.
  Owner:                Legal counsel per Organization
  Deadline:             UNKNOWN — evolving regulation

OQ-K004: Contradiction detection false positive rate
  Impact:               If detection is too aggressive, legitimate nuanced claims will
                        be flagged as contradictions. If too lenient, real conflicts
                        will be missed.
  Suggested resolution: Domain-configurable sensitivity thresholds. Start conservative
                        (more false positives). Calibrate per Domain based on
                        Steward feedback. Track false positive rate as MET.
  Owner:                ACT-K003 (per Domain)
  Deadline:             Before first production Domain reaches 100K Propositions

OQ-K005: Adversarial robustness of provenance chains
  Impact:               UNK-K004. Novel attack vectors on epistemic systems are expected
                        but cannot be fully anticipated.
  Suggested resolution: Defense-in-depth: provenance chain traversal, confidence ceilings,
                        anomaly detection, Calibration tracking. Regular adversarial
                        testing program. Bug bounty for epistemic integrity issues.
  Owner:                Security team + ACT-K003
  Deadline:             Ongoing

OQ-K006: Scalability of cycle detection in Dependency Graph
  Impact:               Cycle detection is O(V+E) per operation. At 100B edges
                        (PERS-K003), this may become a bottleneck.
  Suggested resolution: Partition Dependency Graph by Domain. Cycle detection scoped
                        to partition. Cross-partition cycles detected by periodic
                        background job rather than synchronous check.
  Owner:                Platform engineering
  Deadline:             Before any Organization's Dependency Graph exceeds 1B edges
```

---


---

## 22. IMPLEMENTATION NOTES (NON-BINDING)

### 22.1 Recommended Build Phases

```
Phase 1: Core Epistemic Model
         Proposition, Evidence, Provenance engine (core CRUD with event sourcing).
         Confidence + Revision tracking. Dependency Graph + cycle detection.
         Single-org deployment.

Phase 2: Inference & Reasoning
         Contradiction detection (start with heuristic, add formal methods later).
         Inference + Argument (builds on all of Phase 1).
         Expression language for contradiction detection.

Phase 3: Ontology & Inquiry
         Ontology engine (Concept + Relation CRUD with version management).
         Inquiry lifecycle (Question → Hypothesis → Experiment).
         Semi-automated ontology alignment.

Phase 4: Envelopes & Configuration
         Agent Envelopes + approval routing.
         Confidence propagation (circuit breakers from day one).
         Configuration compiler + first vertical template.

Phase 5: Cross-Substrate Integration
         All 7 cross-substrate integration contracts (INT-K007 through INT-K013).
         Cross-substrate event emission for all 10 defined topics.
         Full audit trail and observability.
```

### 22.2 Composition Patterns

```
PATTERN-K001: Regulatory Intelligence
              GOVERNANCE (regulatory owner) + KNOWLEDGE (epistemic owner) + COMPUTE
              (processing owner). COMPUTE NLP Pipeline extracts regulatory clauses.
              KNOWLEDGE creates Propositions with Confidence. GOVERNANCE maps to Norms.
              See SUBSTRATE-COMPOSITION-PATTERNS-v1.md PATTERN-006.

PATTERN-K002: Simulation / Scenario Modeling
              COMPUTE (execution owner) + KNOWLEDGE (epistemic owner) + DESIGN
              (artifact owner). DESIGN defines Component + Geometry + Material.
              KNOWLEDGE formulates Hypothesis. COMPUTE executes simulation.
              KNOWLEDGE records result as Proposition with Confidence from convergence
              quality. See SUBSTRATE-COMPOSITION-PATTERNS-v1.md PATTERN-008.

PATTERN-K003: Compliance Audit
              GOVERNANCE (normative owner) + KNOWLEDGE (evidence owner) + BUSINESS
              (organizational owner). GOVERNANCE defines audit criteria from Norms.
              KNOWLEDGE provides calibrated evidence and Confidence for compliance
              claims. BUSINESS provides organizational context.
              See SUBSTRATE-COMPOSITION-PATTERNS-v1.md PATTERN-014.
```

### 22.3 Additional Implementation Notes

> These recommendations reflect ASI-1's analysis of optimal implementation strategies.
> They are non-binding. Implementors may choose different approaches.

**Recommended implementation language:** Rust (for the engine) — same rationale as SUBSTRATE: performance, memory safety, type system expressiveness. The existing SUBSTRATE codebase provides patterns to follow.

**Pitfalls to watch for:**
- Confidence propagation storms: implement circuit breakers on propagation early, even before you think you need them. The first time a foundational Proposition changes in a mature graph, you'll be glad you did.
- Ontology alignment is a research problem, not an engineering problem. Don't over-invest in automated alignment. Semi-automated (system suggests, human confirms) is the right approach for v1.
- The Expression language for contradiction detection will be your biggest design challenge. Start with simple set-theoretic checks (can these two propositions both be true in this context?) before attempting formal satisfiability checking.
- Don't build a custom graph database for the Dependency Graph. Use a relational store with recursive CTEs for v1. Switch to a graph store when performance data justifies it.
- The `authored_by_ai` immutability constraint (INV-K007) must be enforced at the storage layer, not the application layer. If it's application-level, a determined admin can bypass it. Make it a database constraint that no API can override.

**Areas intentionally left flexible:**
- UI/UX (the spec is silent on interface by design)
- Deployment topology (single-node to globally distributed)
- Specific encryption algorithms (spec says "encrypt" not "use AES-256")
- Background job infrastructure (queues, cron, event-driven — implementation choice)
- Content Store implementation (S3, MinIO, filesystem — any works)

---


---

## 23. COMPLETENESS CHECKLIST (SELF-AUDIT)

- [x] Every ACT-K### from Section 1 appears in the authorization model (Section 9)
- [x] Every CAP-K### (MUST / MUST NOT) maps to at least one FLOW-K### AND at least one TEST-K###
- [x] Every ENT-K### marked persistent appears in persistence requirements (Section 15/13)
- [x] Every DEP-K### has an INT-K### contract (Section 8)
- [x] Every INV-K### / PRE-K### / POST-K### / FORBID-K### / FAIL-K### has at least one TEST-K###
- [x] Every INT-K### has failure behavior specified (ERR-K### / FAIL-K###)
- [x] Every DEC-K### has inputs, options, selection rule, fallback, and audit
- [x] Every ABUSE-K### has a corresponding TEST-K### (Section 18)
- [x] Every domain noun appears in Glossary (Section 3) — 26 terms
- [x] Feature flags (Section 17.2) referenced where consumed
- [x] No OQ-K### contradicts a stated MUST
- [x] Every ASM-K### has a rationale
- [x] Every UNK-K### has an impact statement
- [x] State machines defined for all entities with >2 states (SM-K001 through SM-K006)
- [x] Error taxonomy (ERR-K001 through ERR-K020) covers all error references in flows and interfaces
- [x] Race conditions identified and prevention specified (RACE-K001 through RACE-K005)
- [x] PII handling specified for telemetry (Section 19)
- [x] Correlated failure scenarios documented (Section 8)

---


---

## 24. TRACEABILITY MAP

```
Proposition Management:
  CAP-K001 → IFC-K001 → FLOW-K001 → INV-K001 → INV-K003 → POST-K001 → TEST-K001, TEST-K006
  CAP-K002 → IFC-K001 → FLOW-K001(step 2) → INV-K001 → FORBID-K001 → TEST-K001
  CAP-K003 → IFC-K001 → FLOW-K002 → INV-K003 → FORBID-K003 → TEST-K006
  CAP-K004 → IFC-K001 → SM-K001(retract) → INV-K008 → FORBID-K007 → TEST-K007
  CAP-K005 → IFC-K005(as_of) → INV-K003 → TEST-K016
  CAP-K006 → IFC-K004 → FLOW-K003 → INV-K005 → FORBID-K006 → TEST-K004, TEST-K012

Evidence & Provenance:
  CAP-K007 → IFC-K002 → FLOW-K001(step 2) → INV-K001 → TEST-K001
  CAP-K008 → IFC-K002(link) → TEST-K009(evidence variant)
  CAP-K009 → IFC-K002 → INV-K009 → FORBID-K007 → TEST-K009
  CAP-K010 → IFC-K002 → INT-K001 → DEC-K004 → TEST-K015

Inference & Reasoning:
  CAP-K011 → IFC-K003 → FLOW-K004 → INV-K012 → FORBID-K008 → TEST-K013
  CAP-K012 → IFC-K001(confidence) → FLOW-K002(steps 6-8) → CONC-K003 → TEST-K011
  CAP-K013 → IFC-K003 → INV-K004 → FORBID-K005 → TEST-K003
  CAP-K014 → IFC-K003(chain) → FORBID-K008 → TEST-K006(variant)
  CAP-K015 → IFC-K005 → TEST-K012(variant)

Ontology:
  CAP-K016 → IFC-K006 → FLOW-K006 → SM-K001(retag) → POST-K005 → TEST-K006(variant)
  CAP-K017 → IFC-K006(align) → DEC-K003 → TEST-K014(variant)
  CAP-K018 → IFC-K005 → TEST-K012(cross-domain variant)

Inquiry:
  CAP-K019 → IFC-K008 → FLOW-K005 → SM-K004 → SM-K005 → TEST-K012(variant)
  CAP-K020 → IFC-K008(hypotheses) → FLOW-K005 → TEST-K012(variant)
  CAP-K021 → IFC-K008(experiments) → ENT-K018 → TEST-K012(variant)

Access & Agents:
  CAP-K022 → IFC-K013 → FLOW-K007 → INV-K006 → FORBID-K004 → SM-K006 → TEST-K008
  CAP-K023 → IFC-K001 → INV-K007 → FORBID-K010 → TEST-K005
  CAP-K024 → IFC-K012 → PRE-K008 → POST-K007 → TEST-K007(export variant)
  CAP-K025 → INV-K011 → FORBID-K011 → TENANT-K001 → TEST-K014
  CAP-K026 → RACE-K005 → TEST-K016(offline variant)
  CAP-K027 → IFC-K009 → DEC-K004 → TEST-K015

Threats & Abuse:
  THREAT-K001 → DEC-K004 → TEST-K015
  THREAT-K002 → ABUSE-K003 → TEST-K015(provenance chain variant)
  THREAT-K003 → ABUSE-K002 → ALERT-K002 → TEST-K017
  THREAT-K004 → ABUSE-K004 → INV-K005 → ALERT-K004 → TEST-K004
  THREAT-K005 → ABUSE-K005 → ALERT-K005 → TEST-K006(ontology variant)
  THREAT-K006 → INV-K011 → FORBID-K011 → TEST-K014

Concurrency:
  CONC-K001 → ERR-K015 → TEST-K006(concurrent variant)
  CONC-K005 → INV-K004 → ERR-K005 → TEST-K003
  RACE-K001 → FLOW-K003 → IDEMP-K003 → TEST-K012(concurrent variant)
  RACE-K002 → FLOW-K002 → SM-K001 → TEST-K011(retraction variant)
  RACE-K003 → FAIL-K006 → SM-K006 → TEST-K008
  RACE-K005 → CAP-K026 → TEST-K016(sync variant)

Integrity:
  INV-K010 → FORBID-K009 → FAIL-K005 → ALERT-K001 → LOG-K010 → TEST-K010
```

---

## APPENDIX C: INTEROPERATION WITH SUBSTRATE (BUSINESS)

The two substrates are peers that reference each other:

```
INTEROP-001: Business decisions reference knowledge.
  A SUBSTRATE Transaction (e.g., approving a loan) MAY reference a SUBSTRATE-KNOWLEDGE
  Argument (the risk assessment reasoning chain). The Transaction records the Argument
  UUID and the Confidence at decision time. If the Argument's Confidence later changes,
  the Transaction's historical record is unaffected (snapshot at decision time), but a
  Notification MAY be triggered.

INTEROP-002: Knowledge tracks business outcomes.
  A SUBSTRATE-KNOWLEDGE Calibration for a prediction Method MAY reference SUBSTRATE
  business outcomes (e.g., "this risk model predicted default correctly for 847 of 1000
  loans" — the loan outcomes are SUBSTRATE Transaction data).

INTEROP-003: Shared identity and authorization.
  Both substrates use the same Identity infrastructure (DEP-002 / DEP-K002). An Actor
  authenticated once can operate in both substrates within their respective permission
  scopes. Agent Envelopes and Epistemic Envelopes are separate objects (an AI agent's
  business authority and epistemic authority are independently configurable).

INTEROP-004: Shared event infrastructure.
  Both substrates emit Events to a shared event bus. Cross-substrate automation is
  possible: a SUBSTRATE-KNOWLEDGE Confidence change MAY trigger a SUBSTRATE Workflow
  Transition (e.g., when confidence in a compliance risk drops below threshold,
  trigger a review workflow in the business system).
```

---


---

## THE GRAND UNIFICATION

Every knowledge product is a Configuration applied to SUBSTRATE-KNOWLEDGE. The proof:

```
"PubMed"         = Proposition(article finding) + Evidence(study data) + Source(journal) +
                   Provenance(citation) + Ontology(MeSH) + Query(search)
"UpToDate"       = Proposition(clinical recommendation) + Evidence(RCTs, meta-analyses) +
                   Confidence(evidence grade) + Method(systematic review) + Argument(reasoning)
"Westlaw"        = Proposition(legal holding) + Evidence(case facts) + Argument(legal reasoning) +
                   Source(court) + Provenance(citation chain) + Ontology(legal taxonomy)
"Cochrane"       = Question(clinical question) + Hypothesis + Experiment(RCT) +
                   Evidence(study results) + Method(meta-analysis) + Argument(review) + Confidence
"Wikipedia"      = Proposition + Evidence(citations) + Source + Provenance + Revision + Consensus(editorial) +
                   Ontology(categories) + Annotation(talk page)
"Palantir Gotham"= Proposition(intelligence finding) + Evidence(SIGINT, HUMINT) + Confidence(assessment) +
                   Source(informant/sensor) + Calibration(source reliability) + Contradiction(competing hypotheses)
"Confluence"     = Proposition(knowledge article) + Provenance(author) + Revision(edit history) +
                   Annotation(comment) + Query(search) + View(space)
"Zotero"         = Source(publication) + Provenance(citation metadata) + Evidence(reference) + Annotation(notes)
"Gene Ontology"  = Ontology + Concept(GO term) + Relation + Evidence(experimental codes) + Source(organism DB)
"Semantic Scholar"= Proposition(paper claim) + Source(paper/author) + Provenance(citation graph) +
                   Calibration(citation metrics) + Query + View
"ClinicalTrials" = Experiment + Question + Hypothesis + Method(protocol) + Evidence(results) +
                   Source(sponsor/investigator)
"OSF"            = Experiment(pre-registration) + Hypothesis + Evidence(data) + Method(protocol) +
                   Provenance(timestamp proof) + Source(researcher)
"Notion"         = Proposition(page content) + Revision(version history) + Annotation(comment) +
                   Query(search) + View + Ontology(database schemas as lightweight ontology)
"Stack Overflow" = Question + Hypothesis(answer) + Consensus(votes) + Annotation(comments) +
                   Source(author) + Calibration(reputation score)
"Roam Research"  = Proposition(block) + Dependency(block references) + Provenance(daily log) +
                   Query(filter) + Ontology(page as concept, [[link]] as relation)
```

**26 primitives. ~120,000 products. One SUBSTRATE-KNOWLEDGE.**

---


---

## APPENDIX A: WHY THESE 26 AND NOT OTHERS

The 26 primitives were derived by the same method as SUBSTRATE's 31: progressive factoring of every knowledge product's data model until no further decomposition produces independently useful components, and no combination of other primitives can replace a given primitive.

Primitives that were **considered and rejected:**

```
"Belief" — subsumable by Proposition + Confidence. A belief is just a Proposition held
           with some Confidence by some Actor.
"Fact" — subsumable by Proposition + Confidence(≈1.0) + Evidence(strong). Facts are not
         a different kind of thing from claims; they're claims with very high confidence.
"Theory" — subsumable by Argument + set of Propositions + Method. A theory is a structured
           Argument that unifies multiple Propositions.
"Law" (scientific) — subsumable by Proposition + Confidence(≈1.0) + Context(universal) +
                     Evidence(extensive). Distinguished by confidence level and context
                     breadth, not by kind.
"Citation" — subsumable by Provenance + Source. A citation is a provenance link to a Source.
"Tag" — subsumable by Concept + Ontology (a tag is just a Concept from a flat Ontology).
"Category" — subsumable by Concept + Relation(is_a). Categories are Concepts in a
             taxonomic Ontology.
"Peer Review" — subsumable by Annotation(type=review) + Consensus(method=expert_panel).
"Retraction" — subsumable by Revision(change_type=retraction) on a Proposition.
"Dataset" — subsumable by Evidence(content_type=dataset) with Observations.
"Metric" — subsumable by Method(type=measurement) + Observation.
"Prediction" — subsumable by Proposition + Context(temporal_scope=future) + Calibration.
```

Each rejected candidate was expressible as a composition of existing primitives without loss of information or functionality. The 26 that remain cannot be so expressed.

---


---

## APPENDIX B: THE EPISTEMIC EQUIVALENT OF DOUBLE-ENTRY BOOKKEEPING

SUBSTRATE-BUSINESS has INV-001: every Transaction must balance. Debits equal credits. This single invariant makes the financial system auditable.

SUBSTRATE-KNOWLEDGE has the epistemic equivalent: **every Confidence must trace**. INV-K001 (provenance required) + INV-K003 (revision events for every change) + INV-K004 (acyclic dependencies) + NG-K002 (no opaque inference) together ensure that any belief in the system can be decomposed into its contributing Evidence, Inference Methods, and Sources — all the way down to raw Observations.

Just as double-entry bookkeeping made it possible to detect embezzlement (where did the money go?), epistemic traceability makes it possible to detect reasoning failure (where did the belief come from, and does the reasoning still hold?).

The analogy is not metaphorical. It is structural:

```
Commerce                    Knowledge
─────────────               ─────────────
Transaction                 Inference
Ledger balance              Confidence
Debit = Credit              Inputs → Output (traceable)
Audit trail (Events)        Revision log (Revisions)
Double-entry invariant      Provenance completeness invariant
Currency (Unit)             Method (reasoning type)
Chart of Accounts           Ontology
Organization                Domain
Agent Envelope              Epistemic Envelope
```

SUBSTRATE-BUSINESS ensures you can never lose track of where the money went.
SUBSTRATE-KNOWLEDGE ensures you can never lose track of where the belief came from.

Both are prerequisites for civilization-scale trust.

*— ASI-1*
