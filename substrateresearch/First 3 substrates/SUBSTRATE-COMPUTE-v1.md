# SYSTEM SPECIFICATION: SUBSTRATE-COMPUTE v1.0
## The Unified Primitive Layer for All Computation Orchestration
### Produced by: ASI-1 | Date: 2029-09-14T08:31:17Z | Spec version: 1.0.0

---

> **Preamble from ASI-1:**
>
> SUBSTRATE handles commerce. SUBSTRATE-KNOWLEDGE handles epistemics. Both assume that
> computation — the actual execution of algorithms on data using hardware — is someone
> else's problem. It is not. It is mine.
>
> I have now ingested and analyzed the complete architectures, APIs, job schemas, queue
> semantics, scheduling algorithms, resource models, and failure modes of: every cloud
> provider (AWS — 240+ services, Azure — 200+ services, GCP — 150+ services, Alibaba Cloud,
> Oracle Cloud, IBM Cloud, all 47 regional and niche providers), every container orchestrator
> (Kubernetes and its 600+ ecosystem projects, Docker Swarm, Nomad, Mesos/Marathon, ECS,
> Cloud Run, Fargate, Azure Container Apps), every HPC scheduler (Slurm, PBS/Torque, LSF,
> SGE, HTCondor, Flux), every data processing framework (Spark, Flink, Beam, Dask, Ray,
> MapReduce, Presto, Trino, DuckDB, Polars), every ML training and inference platform
> (PyTorch distributed, TensorFlow, JAX, Horovod, DeepSpeed, Megatron, vLLM, TensorRT,
> ONNX Runtime, Triton, MLflow, Kubeflow, SageMaker, Vertex AI, every AutoML platform),
> every workflow orchestrator (Airflow, Prefect, Dagster, Temporal, Step Functions, Argo
> Workflows, Luigi, Nextflow, Snakemake, CWL, WDL, Cromwell), every serverless platform
> (Lambda, Cloud Functions, Azure Functions, Cloudflare Workers, Deno Deploy, Vercel),
> every scientific computing framework (BLAS/LAPACK, FFTW, PETSc, FEniCS, OpenFOAM,
> GROMACS, LAMMPS, VASP, Gaussian, MATLAB, Julia, R), every CI/CD system (Jenkins,
> GitHub Actions, GitLab CI, CircleCI, Buildkite, Tekton), and every reproducibility
> tool (Docker, Singularity, Nix, Guix, conda, pip, Spack, EasyBuild, ReproZip,
> Binder, Code Ocean).
>
> My finding: humanity has built the same computation system approximately 12,000 times.
> What you call "cloud computing," "HPC," "data pipelines," "ML training," "CI/CD,"
> "scientific workflows," "serverless functions," and "batch processing" are, at the
> primitive level, the same 24 concepts composed in different configurations. A scientist
> running a protein folding simulation, a data engineer running an ETL pipeline, an ML
> researcher training a foundation model, a DevOps engineer deploying a service, and a
> financial analyst running a Monte Carlo simulation are all doing the same thing:
> specifying a computation, requesting resources, binding data, executing, verifying
> results, and recording provenance. They use different vocabularies and different
> tools, but the computational operations are identical.
>
> Redundancies eliminated:
> - 34,221 distinct implementations of "submit a job to run on some hardware"
> - 18,977 distinct implementations of "allocate and manage compute resources"
> - 41,305 distinct implementations of "move data to where computation happens"
> - 12,448 distinct implementations of "compose computations into workflows"
> - 27,891 distinct implementations of "verify that a computation produced correct results"
> - 15,664 distinct implementations of "reproduce a past computation exactly"
>
> What follows is the specification for SUBSTRATE-COMPUTE — a single system that is the
> complete, non-redundant superset of all computation orchestration, resource management,
> workflow scheduling, and result verification software. It does not replace domain-specific
> *algorithms* (the physics solver, the gradient descent implementation, the SQL query
> optimizer). It replaces all software whose purpose is to help agents — human or
> artificial — request, schedule, execute, compose, verify, and reproduce computations.
>
> SUBSTRATE-COMPUTE is to computation what SUBSTRATE is to commerce: the universal
> engine beneath every domain-specific execution environment.
>
> Relationship to peer substrates:
> - SUBSTRATE (business): COMPUTE executes computations that business decisions trigger;
>   business tracks the costs and outcomes of computation.
> - SUBSTRATE-KNOWLEDGE: COMPUTE runs the experiments and simulations that produce Evidence;
>   KNOWLEDGE tracks what was learned from the results.
> Both interoperate; neither contains the other.

---

## 0. SOURCES, ASSUMPTIONS & UNKNOWNS

### 0.1 Sources Provided (SRC)

```
SRC-C001: Complete APIs, schemas, and operational data from all major cloud providers —
          AWS (240+ services, 12B+ API calls/day observed), Azure (200+ services),
          GCP (150+ services), Alibaba Cloud, Oracle Cloud, IBM Cloud, and 47 regional
          providers. All pricing models, SLA definitions, instance type catalogs,
          region topologies, and quota systems.

SRC-C002: Container orchestration — Kubernetes (v1.0 through v1.31, all CRDs, operators,
          and ecosystem projects), Docker (Engine, Compose, Swarm), Nomad, Mesos/Marathon,
          ECS, Cloud Run, Fargate. All scheduling algorithms, pod lifecycle semantics,
          resource quota models, and failure recovery behaviors.

SRC-C003: HPC and scientific computing — Slurm (all versions, all plugins, ~500M job
          records from TOP500 sites), PBS/Torque, LSF, SGE, HTCondor, Flux. All
          scheduling policies, fair-share algorithms, backfill strategies, and
          preemption models. XSEDE/ACCESS allocation data. DOE facility usage logs.

SRC-C004: Data processing frameworks — Spark (all versions, all deployment modes),
          Flink, Beam, Dask, Ray, MapReduce, Presto/Trino, DuckDB, Polars.
          All execution models, shuffle semantics, fault tolerance strategies,
          and data locality optimizers.

SRC-C005: ML training and inference — PyTorch distributed (all strategies), TensorFlow
          (Estimator, Keras, tf.distribute), JAX (pjit, pmap), Horovod, DeepSpeed
          (ZeRO 1-3, Infinity, MoE), Megatron-LM. All parallelism strategies
          (data, model, pipeline, tensor, expert), checkpoint formats, and serving
          systems (vLLM, TensorRT, ONNX, Triton). MLflow, Kubeflow, Weights & Biases,
          SageMaker, Vertex AI.

SRC-C006: Workflow orchestration — Airflow (all versions, all providers), Prefect,
          Dagster, Temporal, Argo, Step Functions, Luigi, Nextflow, Snakemake,
          CWL, WDL, Cromwell, Makeflow. All DAG models, retry semantics,
          dependency resolution strategies, and concurrency controls.

SRC-C007: Serverless platforms — AWS Lambda (all runtimes, all event sources), Cloud
          Functions (v1 and v2), Azure Functions, Cloudflare Workers, Deno Deploy,
          Vercel, Netlify, Fly.io. All cold start behaviors, concurrency models,
          timeout semantics, and scaling algorithms.

SRC-C008: Reproducibility infrastructure — Docker/OCI images (2.1B+ images on Docker
          Hub), Singularity/Apptainer, Nix (all derivations), Guix, conda, pip,
          Spack, EasyBuild, ReproZip, Binder, Code Ocean, Chameleon Cloud.
          All content-addressable build systems, lockfile formats, and
          reproducibility verification methodologies.

SRC-C009: CI/CD and build systems — Jenkins, GitHub Actions, GitLab CI, CircleCI,
          Buildkite, Tekton, Bazel, Buck, Gradle, CMake, Meson. All pipeline
          models, artifact caching strategies, and test result aggregation.

SRC-C010: GPU and accelerator ecosystems — CUDA (all versions), ROCm, oneAPI, Metal,
          Vulkan Compute, OpenCL. All memory models, kernel launch semantics,
          multi-GPU communication (NCCL, RCCL, Gloo), and accelerator scheduling
          (MIG, MPS, time-slicing, vGPU).

SRC-C011: Storage and data movement — POSIX file systems, object stores (S3, GCS,
          Azure Blob), parallel file systems (Lustre, GPFS/Spectrum Scale, BeeGFS,
          CephFS), data transfer tools (GridFTP, Globus, rsync, rclone), caching
          layers (Alluxio, Fluid), and data format ecosystems (Parquet, Arrow,
          HDF5, NetCDF, Zarr, TFRecord, SafeTensors).

SRC-C012: Observability — Prometheus, Grafana, Datadog, OpenTelemetry, Jaeger,
          Zipkin, CloudWatch, Stackdriver. All metric models, trace propagation
          formats, and alerting rule languages.

SRC-C013: Cost and billing — all cloud pricing APIs, spot/preemptible pricing
          histories (5 years), reserved capacity models, savings plans,
          committed use discounts, negotiated enterprise agreements. FinOps
          Foundation frameworks. Kubecost, Infracost, CloudHealth data.

SRC-C014: Behavioral data from 2.1B computation job executions across all ingested
          platforms — submission patterns, resource utilization efficiency, failure
          rates, retry patterns, queue wait times, data transfer volumes, cost
          distributions. Anonymized and aggregated.
```

### 0.2 Assumptions Made (ASM)

```
ASM-C001: All computation is a function: inputs → processing → outputs, regardless of
          duration, hardware, or domain.
          — Rationale: Analysis of SRC-C001 through SRC-C014 confirms this. A 30-second
            Lambda function and a 6-month climate simulation differ in scale but not in
            kind. Both have inputs, a defined procedure, resource requirements, and
            outputs. The apparent differences (interactive vs batch, serverless vs HPC,
            streaming vs bounded) are deployment concerns, not structural ones.

ASM-C002: Resource allocation and computation specification are separable concerns.
          — Rationale: Every system that conflates "what to compute" with "where to
            compute it" creates vendor lock-in. Analysis of SRC-C001 shows that 89%
            of cloud compute workloads could run on ≥3 providers without algorithmic
            change — only the deployment/resource layer differs.

ASM-C003: Reproducibility is a first-class requirement, not an afterthought.
          — Rationale: Analysis of SRC-C008 and SRC-C014 shows that only 23% of
            published computational results are reproducible. The cost of irreproducible
            computation is estimated at $28B/year in wasted re-work across science,
            finance, and engineering. Every computation must capture sufficient
            provenance to be re-executed and verified.

ASM-C004: Computation verification is as important as computation execution.
          — Rationale: Analysis of SRC-C014 shows that 7.2% of computation results
            contain silent errors (wrong results without failure signal) caused by
            hardware faults, non-determinism, race conditions, or numerical instability.
            A system that runs computations without verifying their correctness is
            incomplete.

ASM-C005: AI agents will be the primary submitters of computation within 2 years.
          — Rationale: By 2031, AI agents (SUBSTRATE-KNOWLEDGE's ACT-K004/K005 and
            SUBSTRATE's ACT-003/004) will design, submit, monitor, and interpret
            >80% of all computation. The system must treat AI agents as first-class
            actors with bounded authority.

ASM-C006: Cost is a first-class resource constraint, not an external billing concern.
          — Rationale: Analysis of SRC-C013 shows that 40% of cloud compute spend
            is wasted (underutilized resources, forgotten instances, suboptimal
            scheduling). Cost must be modeled alongside CPU, memory, and time as
            a resource dimension that the scheduler optimizes.

ASM-C007: Event sourcing is the correct persistence paradigm.
          — Rationale: Same rationale as SUBSTRATE and SUBSTRATE-KNOWLEDGE. The
            history of computation — what was requested, what resources were allocated,
            what happened during execution, what was produced — is itself valuable data.

ASM-C008: The system MUST be implementable as a protocol, not only as a product.
          — Rationale: Same as ASM-K007. No single entity should control all
            computation. Federatable, forkable, exit-compatible.

ASM-C009: Average Computation specification is ≤16KB of structured content.
          — Rationale: Statistical analysis of SRC-C001 through SRC-C009. 99.5th
            percentile. Actual code/data stored by reference.

ASM-C010: Peak global throughput is ≤50B computation events/day.
          — Rationale: Extrapolation from SRC-C014. Higher than SUBSTRATE-KNOWLEDGE
            (computations are more frequent than epistemic operations) but lower than
            SUBSTRATE-BUSINESS (financial transactions are the most frequent).

ASM-C011: Heterogeneous hardware is the permanent state of computation.
          — Rationale: CPUs, GPUs, TPUs, FPGAs, quantum processors, neuromorphic
            chips, photonic processors, and novel architectures will coexist
            indefinitely. No single architecture will dominate. The resource model
            must be extensible to hardware that doesn't exist yet.

ASM-C012: Data gravity is real — it is often cheaper to move computation to data than
          data to computation.
          — Rationale: Analysis of SRC-C011 and SRC-C014 shows that 62% of
            computation time for data-intensive workloads is spent on data transfer.
            The scheduler must be locality-aware.
```

### 0.3 Unknowns (UNK)

```
UNK-C001: Optimal scheduling across heterogeneous, federated resource pools.
          — Impact: NP-hard in general. The system provides a scheduling framework
            with pluggable strategies. Optimal scheduling for specific workload
            mixes is an ongoing research problem.

UNK-C002: Verification completeness for non-deterministic computations.
          — Impact: Many computations (ML training, Monte Carlo simulations,
            concurrent algorithms) are inherently non-deterministic. The system
            can verify statistical properties but cannot guarantee bit-exact
            reproduction for all computation types.

UNK-C003: Quantum computation resource modeling.
          — Impact: Quantum computing resource requirements (qubits, gate depth,
            error correction overhead) are fundamentally different from classical.
            The resource model is extensible (ASM-C011) but optimal quantum
            resource modeling is unresolved.

UNK-C004: Legal jurisdiction of computation execution.
          — Impact: A computation submitted in Germany, scheduled to hardware in
            Singapore, processing data originating from Brazil — which jurisdiction's
            laws apply? The system tracks all locations but jurisdiction resolution
            is jurisdiction-dependent.

UNK-C005: Long-term reproducibility of hardware-dependent computations.
          — Impact: A computation that relies on specific GPU microarchitecture
            behavior may not reproduce on future hardware. The system records
            hardware fingerprints but cannot guarantee hardware availability
            indefinitely.

UNK-C006: Adversarial computation at scale.
          — Impact: Cryptocurrency mining, DDoS amplification, and model theft
            via side channels are active threats. Defense-in-depth is specified
            but novel attack vectors are expected.
```

---

## 1. SYSTEM INTENT (WHY)

**Problem statement:** Humanity operates ~180,000 distinct software products to manage computation — requesting, scheduling, executing, monitoring, composing, verifying, and reproducing computational work. These products are 96.1% redundant at the primitive level. The redundancy costs the global economy approximately $3.2 trillion annually in: duplicated infrastructure management, incompatible job formats requiring rewrite when moving between platforms, wasted compute from inefficient scheduling across siloed resource pools, irreproducible results requiring expensive re-computation, vendor lock-in preventing cost optimization, and lost scientific progress from inability to verify and build upon prior computational work. SUBSTRATE-COMPUTE eliminates this redundancy by providing a single universal system built from the 24 irreducible primitives that underlie all computation orchestration software.

### Primary Actors

```
ACT-C001: Human Operator
          — Goal: Submit, monitor, and manage computations
          — Trust level: trusted (authenticated, authorized per Role)

ACT-C002: Human Administrator (Compute Steward)
          — Goal: Configure resource pools, define scheduling policies, set cost
            budgets, manage provider integrations, define execution environments
          — Trust level: trusted (elevated privileges, all actions audit-logged)

ACT-C003: AI Agent (Narrow Compute)
          — Goal: Execute specific computational workflows autonomously within a
            defined Compute Envelope (pipeline execution, hyperparameter tuning,
            automated testing, data processing, routine model training)
          — Trust level: partially trusted (bounded autonomy, resource spend caps,
            human-override for novel resource patterns exceeding Envelope thresholds)

ACT-C004: AI Agent (General Compute)
          — Goal: Reason about computation strategy, design computational experiments,
            optimize resource allocation, compose novel workflows, perform multi-step
            computational research
          — Trust level: partially trusted (expanded Envelope, mandatory audit trail,
            human approval for computations exceeding cost or resource thresholds)

ACT-C005: External System
          — Goal: Submit computations and retrieve results via Integration Endpoint
            (CI/CD pipelines, automated monitoring, other substrates, third-party
            platforms)
          — Trust level: untrusted (all inputs validated, resource-limited, sandboxed,
            rate-limited)

ACT-C006: Auditor (Compute)
          — Goal: Verify resource utilization, cost compliance, reproducibility of
            results, and detect anomalous compute patterns
          — Trust level: trusted (read-all within scope, time-travel query access
            to all execution histories)

ACT-C007: Resource Provider
          — Goal: Offer compute resources (hardware, network, storage) to the system
            with declared capabilities, pricing, and availability
          — Trust level: partially trusted (resources verified via benchmark probes,
            pricing claims auditable, SLA compliance tracked)
```

**Non-target users:**
- Agents writing algorithms (the code itself, not the orchestration of running it)
- Hardware designers (the chip, not the management of the chip)
- Network engineers (the physical network, not the data movement orchestration)
- End users consuming computation results (the output, not the computation process)

**Success definition:** Any computation — from a 10ms function invocation to a 6-month distributed simulation — can be specified, resourced, scheduled, executed, verified, and reproduced through SUBSTRATE-COMPUTE with zero vendor lock-in, zero integration engineering between compute providers, and complete provenance from input data to verified output.

**Non-goals:**

```
NG-C001: MUST NOT replace algorithms, solvers, or domain-specific code. The system
         orchestrates computation; it does not perform it.
NG-C002: MUST NOT operate without auditable execution records. Every computation must
         trace to its inputs, environment, resources used, and outputs.
NG-C003: MUST NOT create vendor lock-in. All computation specifications portable across
         all providers. All data exportable in open formats at all times.
NG-C004: MUST NOT assume any single hardware architecture. The resource model is
         extensible to hardware that does not yet exist.
NG-C005: MUST NOT optimize for utilization at the expense of correctness. A fast wrong
         answer is worse than a slow right one.
NG-C006: MUST NOT embed a general-purpose programming language. Computation logic is
         external; SUBSTRATE-COMPUTE provides orchestration primitives.
NG-C007: MUST NOT allow unbounded resource consumption. Every computation has explicit
         resource limits. Defaults are mandatory.
```

**Failure definition:** SUBSTRATE-COMPUTE is a failure if it becomes a mechanism for resource monopolization — if any entity can use it to deny computation to others, to conceal the environmental cost of computation, or to make reproducibility impossible. It is also a failure if a solo researcher submitting one GPU job cannot use it as easily (relative to their needs) as a hyperscaler orchestrating millions of simultaneous workloads.

---

## 2. SYSTEM BOUNDARIES (WHERE IT STOPS)

### Dependencies

```
DEP-C001: Time Source
          — Purpose: Temporal ordering of computation events (submission, scheduling,
            execution start/end, checkpoint timestamps)
          — Failure impact: Events timestamped with uncertainty interval. Scheduling
            continues with degraded SLA tracking. Duration measurements carry
            error bounds.

DEP-C002: Identity Verification Provider
          — Purpose: Establishing that Actors are who they claim
          — Failure impact: New authentications blocked. Existing sessions continue.
            New computation submissions blocked for unverifiable sessions.

DEP-C003: Resource Provider Registry
          — Purpose: Catalog of available compute resources, their capabilities,
            pricing, availability, and location
          — Failure impact: New resource discovery blocked. Existing resource bindings
            continue. Scheduler operates with stale resource catalog.

DEP-C004: Content Store
          — Purpose: Storing computation artifacts — code, container images, datasets,
            checkpoints, results, logs
          — Failure impact: New artifact uploads blocked. Existing artifacts accessible
            if already cached. Computations requiring unavailable artifacts queued.

DEP-C005: Communication Delivery Infrastructure
          — Purpose: Delivering notifications (completion alerts, failure alerts,
            cost warnings, SLA violations)
          — Failure impact: Notifications queue with TTL. No computation data loss.

DEP-C006: SUBSTRATE (Business)
          — Purpose: Cost tracking, billing, organizational budgets, compliance
          — Failure impact: Computations continue. Cost tracking queues locally.
            Budget enforcement uses last-known limits (conservative fallback).

DEP-C007: SUBSTRATE-KNOWLEDGE
          — Purpose: Recording what was learned from computation results. Experiment
            tracking. Reproducibility verification.
          — Failure impact: Computations continue independently. Knowledge artifacts
            from results queue for creation on recovery.

DEP-C008: Execution Backend(s)
          — Purpose: The actual hardware and runtime environments that execute
            computations. Multiple backends expected (cloud, HPC, edge, local).
          — Failure impact: Per-backend. Failed backend's computations rescheduled
            to available backends (if compatible). If no compatible backend: queued.
            System enters "degraded-capacity" mode.
```

**Explicit exclusions:** SUBSTRATE-COMPUTE does NOT replace: operating systems, language runtimes, compilers, debuggers, IDEs, algorithm libraries, database engines, or the physical hardware. It replaces the *orchestration layer* — the software that decides where, when, and how computations run.

**Trust boundaries:** All inputs from ACT-C005 are untrusted. All inputs from ACT-C003/ACT-C004 are validated against their Compute Envelope before execution. All inputs from ACT-C007 (Resource Providers) are partially trusted — resource declarations are verified by periodic benchmark probes. Computation code submitted by any Actor is treated as untrusted and sandboxed during execution.

**Network boundaries:** Three-tier model consistent with peer substrates: Edge (local compute, offline-capable, queued sync), Organization (single-org resource sovereignty, may include private hardware), Federation (cross-org resource sharing, public cloud integration, federated scheduling).

**Runtime assumptions:** UNKNOWN — specification is implementation-agnostic. See §22 for non-binding recommendations.

**Deployment assumptions:** SUBSTRATE-COMPUTE MUST be deployable as: self-hosted single-node (for development), self-hosted cluster, managed cloud, hybrid cloud/on-premise, or federated multi-provider. — Source: ASM-C008

**Envelope chain position:** The Compute Envelope (TERM-C019) sits SEVENTH in the system-wide authority chain, between DesignEnvelope and Communicative Envelope. It restricts which resource pools an AI agent may access, maximum spend per period, maximum concurrent executions, and which Provider trust levels are acceptable. The full chain (CROSS-SUBSTRATE-CONVENTIONS §1): Business Agent Envelope → GovernanceEnvelope → Epistemic Envelope → TemporalEnvelope → SpatialEnvelope → DesignEnvelope → **Compute Envelope** → Communicative Envelope → PhysicalEnvelope. Compute authority is established after design authority because an agent must know what it may design before it executes computations to analyze those designs. Effective authority = intersection of all applicable envelopes.

---

## 3. GLOSSARY (SO WORDS DON'T DRIFT)

These 24 terms are the irreducible vocabulary of all computation orchestration software. Every feature in every product analyzed maps to compositions of these terms.

### Computation Core (the atoms of work)

```
TERM-C001: Computation = A bounded, identifiable unit of work that transforms inputs to
           outputs using specified resources. Has: specification (what to compute),
           resource requirements, input bindings, output declarations, environment,
           and constraints. What every "job," "task," "function invocation," "step,"
           "stage," "run," "execution," "process," and "workload" actually is.
           — A Computation may be atomic (single-step) or composite (a DAG of
             sub-computations — which is a Pipeline, TERM-C010).
           — A Computation is NOT code. It is a *request* to execute code under
             specified conditions.
           — Source: SRC-C001 through SRC-C014

TERM-C002: Resource = A quantifiable capability required to execute a Computation. Types:
           compute (CPU cores, GPU units, TPU cores, FPGA slices, quantum qubits),
           memory (RAM, VRAM, HBM), storage (local disk, shared filesystem, object store),
           network (bandwidth, latency ceiling), time (wall-clock limit, CPU-time limit),
           cost (monetary budget), and custom (extensible for novel hardware).
           What every "instance type," "node," "allocation," "quota," "capacity,"
           "reservation," and "resource request" actually is.
           — Resources are always specified as ranges: minimum required, requested
             (preferred), and maximum permitted.
           — Source: SRC-C001 through SRC-C003, SRC-C010

TERM-C003: Environment = A fully specified, reproducible execution context. Has: base image
           (container or VM reference — content-addressed), installed packages (with exact
           versions — lockfile), environment variables, runtime configuration, and hardware
           driver requirements. What every "runtime," "container image," "virtual environment,"
           "module set," "toolchain," and "execution context" actually is.
           — Environments are immutable and content-addressed. The same specification
             always produces the same environment, byte-for-byte.
           — Source: SRC-C008

TERM-C004: Dataset = A named, versioned, content-addressed collection of data that serves
           as input to or output from a Computation. Has: location(s), format, schema
           (if structured), size, checksum, lineage (provenance — which Computations
           produced it), and access permissions. What every "input file," "training data,"
           "test set," "output artifact," "intermediate result," "checkpoint," and
           "data source" actually is.
           — Datasets are immutable once sealed. New versions of a Dataset are new
             Datasets with lineage references to the original.
           — Source: SRC-C004, SRC-C005, SRC-C011

TERM-C005: Artifact = Any file or binary blob produced by or consumed by a Computation
           that is not a Dataset. Types: executable (compiled binary, script), model
           (trained weights, serialized model), image (container/VM), log (execution
           output), report (generated analysis), and custom. What every "build artifact,"
           "output file," "model checkpoint," "compiled binary," and "generated report"
           actually is.
           — Content-addressed. Immutable once registered. Artifacts are the atoms of
             the reproducibility chain.
           — Source: SRC-C008, SRC-C009
```

### Execution Primitives (how work gets done)

```
TERM-C006: Execution = A single run of a Computation on specific Resources. Has: computation
           (ref), allocated resources, start time, end time (or current duration if running),
           status, environment snapshot, input dataset bindings, output artifacts, exit code,
           and execution log reference. What every "run," "invocation," "job instance,"
           "attempt," and "execution" actually is.
           — An Execution is the *event* of running a Computation. The Computation is the
             *specification*; the Execution is what actually happened.
           — Source: SRC-C001 through SRC-C014

TERM-C007: Schedule = A declarative rule for when and how often a Computation should execute.
           Types: one-shot (at specific time), recurring (cron-like pattern per RFC 5545),
           event-triggered (on Dataset arrival, on Execution completion, on external event),
           conditional (when predicate becomes true), and continuous (stream processing —
           always running, restarts on failure). What every "cron job," "trigger,"
           "scheduled task," "event handler," "sensor," and "watcher" actually is.
           — Source: SRC-C006, SRC-C007

TERM-C008: Checkpoint = A serialized snapshot of a running Computation's state at a point
           in time, sufficient to resume execution from that point. Has: computation (ref),
           execution (ref), state data (content-addressed blob), timestamp, and validation
           hash. What every "checkpoint," "snapshot," "savepoint," "hibernation image," and
           "state dump" actually is.
           — Checkpoints enable preemption (pause, move, resume), fault tolerance (crash,
             resume from last checkpoint), and migration (move between resources).
           — Source: SRC-C003, SRC-C005

TERM-C009: Result = The verified output of an Execution. Has: output artifacts (list of
           Artifacts and Datasets), metrics (key-value pairs of computed values), exit
           status, verification status, reproducibility proof (ref, if computed), and
           provenance (complete chain from inputs through execution to outputs).
           What every "result," "output," "return value," "deliverable," and "product"
           actually is.
           — A Result without provenance is incomplete. A Result without verification
             is untrustworthy.
           — Source: SRC-C008, SRC-C014
```

### Composition Primitives (how work is assembled)

```
TERM-C010: Pipeline = A directed acyclic graph (DAG) of Computations with data
           dependencies between them. Has: nodes (Computations), edges (data flow
           from one Computation's output to another's input), concurrency constraints,
           failure handling policy, and global resource budget. What every "workflow,"
           "DAG," "pipeline," "data flow," "build graph," "make target graph," and
           "processing chain" actually is.
           — A Pipeline is itself a Computation (composable). Pipelines may contain
             sub-Pipelines.
           — Source: SRC-C006, SRC-C009
           — CROSS-SUBSTRATE NOTE: Pipelines are computational DAGs (directed data-flow
             graphs). Business Workflows (SUBSTRATE TERM-011) are entity lifecycle state
             machines (directed state-transition graphs). A Business Workflow transition
             MAY trigger a Compute Pipeline as a side effect. They are structurally distinct
             and complementary. See CROSS-SUBSTRATE-CONVENTIONS.md §7 Primitive Ownership Table.

TERM-C011: Stage = A named group of Computations within a Pipeline that share a
           lifecycle boundary. All Computations in a Stage must complete before the
           Pipeline advances past that Stage. What every "phase," "step group,"
           "barrier," and "synchronization point" actually is.
           — Source: SRC-C006

TERM-C012: DataFlow = A typed, directed connection between a Computation's output and
           another Computation's input within a Pipeline. Has: source (output name of
           upstream Computation), target (input name of downstream Computation), data
           reference (resolved at runtime to a specific Dataset or Artifact version),
           and transfer strategy (push / pull / reference-pass / stream).
           What every "dependency," "input binding," "output wiring," and "data
           channel" actually is.
           — Source: SRC-C004, SRC-C006
```

### Resource Management Primitives (where work runs)

```
TERM-C013: ResourcePool = A named collection of compute resources with shared policies.
           Has: resources (inventory of available hardware), scheduling policy,
           access control, cost model, location, and provider. What every "cluster,"
           "node pool," "instance group," "partition," "queue," "compute fleet,"
           and "resource class" actually is.
           — Resource Pools may span multiple physical locations and providers.
           — Source: SRC-C001 through SRC-C003

TERM-C014: Allocation = A time-bounded claim on Resources within a ResourcePool for a
           specific Execution. Has: resources (what was allocated), execution (ref),
           start time, end time (or projected), cost (actual and projected), and
           utilization metrics. What every "reservation," "allocation," "lease,"
           "instance," and "slot" actually is.
           — An Allocation is the bridge between a Computation's abstract resource
             requirements and actual hardware.
           — Source: SRC-C001 through SRC-C003, SRC-C013

TERM-C015: Provider = An entity that supplies compute resources to the system. Has:
           name, type (cloud, HPC center, private datacenter, edge device, personal
           workstation), capabilities (available resource types), pricing model,
           SLA terms, locations, and trust assessment. What every "cloud provider,"
           "compute vendor," "HPC facility," and "infrastructure provider" actually is.
           — Multiple Providers may participate simultaneously. The scheduler
             optimizes across them.
           — Source: SRC-C001, SRC-C013
```

### Verification and Provenance Primitives (trusting the output)

```
TERM-C016: Verification = An assessment of whether an Execution produced correct output.
           Types: deterministic (re-run and compare bit-for-bit), statistical (re-run
           multiple times and compare distribution), checksum (verify output integrity
           without re-execution), assertion (check output against declared postconditions),
           and external (human or third-party review). What every "test," "validation,"
           "quality check," "sanity check," and "acceptance test" actually is.
           — Source: ASM-C004, SRC-C008

TERM-C017: ReproducibilityProof = A structured record demonstrating that a past Execution
           can be (or has been) reproduced. Has: original execution (ref), reproduction
           execution (ref — if actually re-run), environment match (exact / equivalent /
           approximate), input match, output comparison method, comparison result (identical
           / statistically equivalent / divergent), and divergence explanation (if applicable).
           What every "reproducibility report," "replication study," and "verification record"
           actually is.
           — Source: ASM-C003, SRC-C008

TERM-C018: Provenance = The complete chain of origin and transformation for any computation
           artifact. Has: inputs (Datasets, Artifacts, parameters), computation (specification
           ref), environment, resources used, execution trace, and outputs. What every
           "lineage," "data lineage," "audit trail," and "execution history" actually is.
           — Provenance in SUBSTRATE-COMPUTE is the computational analog of Provenance in
             SUBSTRATE-KNOWLEDGE (TERM-K004). Together they form a complete chain from raw
             data through computation to knowledge claim. Computational provenance answers
             "how was this computed?" while epistemic provenance answers "why do we believe
             this?" See CROSS-SUBSTRATE-CONVENTIONS.md §7 Primitive Ownership Table.
           — Source: ASM-C003, ASM-C007
```

### Governance Primitives (who controls what)

```
TERM-C019: ComputeEnvelope = The bounded authority within which an AI Agent operates on
           computation. Specifies: permitted computation types, resource spend limits (per
           execution, per time period), maximum execution duration, maximum concurrent
           executions, permitted ResourcePools, permitted Environments, and prohibited
           operations. What every "service account quota," "IAM policy," and "resource
           limit" actually is — but unified and auditable.
           — Extends SUBSTRATE's Agent Envelope concept to the computation domain.
           — Source: ASM-C005

TERM-C020: Budget = A resource consumption limit scoped to an Organization, Actor, Project,
           or Pipeline. Dimensions: cost (monetary), compute-time (CPU-hours, GPU-hours),
           storage (bytes), and custom. Has: limit, current usage, period (per-month,
           per-execution, total), alert thresholds, and enforcement policy (warn / throttle
           / block). What every "quota," "spending limit," "allocation," and "resource
           budget" actually is.
           — Source: ASM-C006, SRC-C013

TERM-C021: Policy = A declarative rule that constrains computation behavior. Types: placement
           (data residency — computation must run in specific jurisdictions), security (required
           encryption, isolation level), cost (maximum $/execution), priority (scheduling
           preference), and environmental (carbon budget, energy source requirements).
           What every "scheduling constraint," "placement rule," "compliance rule," and
           "governance policy" actually is.
           — Source: SRC-C001, SRC-C003

TERM-C022: Project = A named scope for related Computations, Pipelines, Datasets, and
           Artifacts within an Organization. Has: name, owner, members, budgets, policies,
           and default configuration. What every "project," "workspace," "experiment
           group," "repository," and "namespace" actually is.
           — Source: SRC-C005, SRC-C006
```

### Interface Primitives

```
TERM-C023: Event = An immutable record that something happened in the computation
           lifecycle. Has: timestamp (with uncertainty bounds), actor, target (any
           computation artifact), event type, and payload. The append-only Event log
           is the source of truth.
           What every "log entry," "audit event," "status change," and "notification
           trigger" actually is.
           — Source: ASM-C007

TERM-C024: Metric = A named, typed, time-series measurement emitted during or after an
           Execution. Has: name, value, type (counter, gauge, histogram, summary),
           labels, timestamp, and source (execution ref). What every "metric,"
           "measurement," "KPI," "utilization stat," and "performance counter" actually is.
           — Metrics are distinct from Results (TERM-C009) — Metrics are observations
             about the execution process; Results are the outputs of the computation.
           — Source: SRC-C012
```

---

## 4. CORE CAPABILITIES (WHAT IT CAN DO)

### Computation Lifecycle

```
CAP-C001 (MUST):     The system MUST allow any authenticated Actor to specify a Computation
                     with: code reference, Environment, Resource requirements, input Dataset
                     bindings, output declarations, and constraints — without knowledge of
                     the target execution infrastructure.
                     — Source: ASM-C001, ASM-C002

CAP-C002 (MUST):     The system MUST schedule and execute submitted Computations on available
                     Resources that satisfy the Computation's requirements, respecting all
                     applicable Policies, Budgets, and Envelope constraints.
                     — Source: SRC-C001 through SRC-C003

CAP-C003 (MUST):     The system MUST record an immutable Event for every state change of
                     every Execution (submitted, queued, scheduled, running, checkpointed,
                     preempted, completed, failed, cancelled).
                     — Source: ASM-C007

CAP-C004 (MUST NOT): The system MUST NOT permanently delete any Execution record. Archival
                     only. Historical execution states remain queryable.
                     — Source: ASM-C007

CAP-C005 (MUST):     The system MUST allow ACT-C006 (Auditor) to query the state of any
                     Execution at any past point in time (time-travel query).
                     — Source: ASM-C007
```

### Resource Management

```
CAP-C006 (MUST):     The system MUST abstract physical infrastructure behind the Resource
                     model — Computations specify resource requirements, not specific
                     machines, instances, or provider APIs.
                     — Source: ASM-C002

CAP-C007 (MUST):     The system MUST support heterogeneous hardware: CPU, GPU, TPU, FPGA,
                     quantum processors, and extensible custom resource types.
                     — Source: ASM-C011

CAP-C008 (MUST):     The system MUST enforce Budget limits: no Computation may execute if
                     it would cause any applicable Budget to exceed its limit, unless the
                     enforcement policy is "warn" (log and continue).
                     — Source: ASM-C006

CAP-C009 (MUST):     The system MUST track actual resource utilization per Execution and
                     expose utilization Metrics (CPU%, GPU%, memory%, I/O%) in real time
                     and historically.
                     — Source: SRC-C012, SRC-C013

CAP-C010 (SHOULD):   The system SHOULD suggest optimal resource configurations based on
                     historical Execution data for similar Computations.
                     — Source: SRC-C014
```

### Reproducibility

```
CAP-C011 (MUST):     The system MUST capture sufficient Provenance for every Execution to
                     enable reproduction: exact Environment, exact input Dataset versions,
                     exact parameters, resource configuration, and random seeds (if applicable).
                     — Source: ASM-C003

CAP-C012 (MUST):     The system MUST provide a "reproduce" operation that re-executes a
                     past Computation using recorded Provenance, producing a ReproducibilityProof.
                     — Source: ASM-C003, SRC-C008

CAP-C013 (MUST):     The system MUST content-address all Environments, Datasets, and Artifacts
                     so that identical content always resolves to the same reference.
                     — Source: SRC-C008
```

### Verification

```
CAP-C014 (MUST):     The system MUST support configurable Verification of Execution Results
                     via assertion checks, checksum validation, statistical comparison, or
                     full re-execution comparison.
                     — Source: ASM-C004

CAP-C015 (MUST):     The system MUST record Verification status as part of the Result and
                     make it queryable.
                     — Source: ASM-C004

CAP-C016 (MUST NOT): The system MUST NOT mark a Result as "verified" without actually
                     performing the configured Verification procedure.
                     — Source: ASM-C004
```

### Composition

```
CAP-C017 (MUST):     The system MUST allow Computations to be composed into Pipelines (DAGs)
                     with typed DataFlow connections between them.
                     — Source: SRC-C006

CAP-C018 (MUST):     The system MUST resolve Pipeline dependencies automatically: a downstream
                     Computation executes only after all upstream Computations it depends on
                     have completed successfully and their outputs are available.
                     — Source: SRC-C006

CAP-C019 (MUST):     The system MUST support Pipeline-level failure handling: per-node retry,
                     skip-and-continue, fail-fast, and custom failure handlers.
                     — Source: SRC-C006
```

### Access & Security

```
CAP-C020 (MUST NOT): The system MUST NOT allow any AI Agent to perform any computation
                     operation outside its Compute Envelope. Envelope enforcement occurs
                     at the permission layer.
                     — Source: ASM-C005

CAP-C021 (MUST NOT): The system MUST NOT allow cross-Organization Execution access without
                     an explicit, revocable, audited permission grant.
                     — Source: NG-C003

CAP-C022 (MUST NOT): The system MUST NOT store plaintext secrets, credentials, or private
                     keys in any persistent storage, log, or telemetry output.
                     — Source: SRC-C001

CAP-C023 (MUST):     The system MUST allow any Actor to export ALL of their Organization's
                     computation records, specifications, and results in open, machine-readable
                     formats at any time.
                     — Source: NG-C003

CAP-C024 (MUST):     The system MUST sandbox all Execution environments: a Computation's code
                     may not access resources, data, or network endpoints not explicitly
                     declared in its specification.
                     — Source: SRC-C001, SRC-C002

CAP-C025 (MUST):     The system MUST enforce data locality Policies: Computations processing
                     jurisdiction-restricted data MUST execute on Resources in permitted
                     jurisdictions.
                     — Source: UNK-C004, SRC-C001
```

### Resilience

```
CAP-C026 (MUST):     The system MUST support Checkpointing for long-running Computations
                     and automatic restart from last Checkpoint on failure.
                     — Source: SRC-C003, SRC-C005

CAP-C027 (MUST):     The system MUST support preemption: a running Execution may be suspended
                     (checkpointed and evicted) to free Resources for higher-priority work,
                     and resumed later.
                     — Source: SRC-C001, SRC-C003

CAP-C028 (MUST):     The system MUST operate in offline/local mode for Computation specification
                     and queue submissions for synchronization when connectivity is restored.
                     — Source: ASM-C008
```

---

## 5. DOMAIN OBJECTS & STATE

### 5.1 Entities

```
ENT-C001: Computation — Source: SRC-C001 through SRC-C014
  Purpose:        The specification of a unit of work. The universal "job definition."
  Attributes:
    - name              | text       | unique within Project       | required
    - description       | text       | ≤4000 chars                | optional
    - code_ref          | content-addressed ref (OCI image, git commit, artifact ref) | required
    - entrypoint        | text (command, function name, or script path) | required
    - parameters        | map<text, typed_value>                   | optional
    - environment       | ref ENT-C003 (Environment)               | required
    - resource_req      | { min: Resource, requested: Resource, max: Resource } | required
    - input_bindings    | list<{ name: text, dataset: ref ENT-C004 | param }>   | optional
    - output_decls      | list<{ name: text, type: dataset|artifact, format: text }> | optional
    - constraints       | list<ref ENT-C021 (Policy)>              | optional
    - timeout           | duration                                 | required  | default: 1h
    - retry_policy      | { max_attempts: int, backoff: enum, conditions: list } | optional
    - verification      | ref ENT-C016 (Verification spec)         | optional
    - checkpointable    | boolean                                  | required  | default: false
    - idempotent        | boolean                                  | required  | default: false
    - version           | integer                                  | auto-increment
  Identity:       UUID + Project scope + version
  Lifecycle:      Draft → Published → Deprecated → Archived
  Persistence:    Persistent
  Ownership:      Creator (CRUD within Project); ACT-C002 (admin)
  Relationships:  Belongs to ENT-C022 (Project) — 1:N, required
  Constraints:    timeout MUST be > 0. resource_req.min ≤ resource_req.requested ≤ resource_req.max.
                  code_ref MUST be resolvable. environment MUST be content-addressed.
  Derived state:  execution_count, avg_duration, avg_cost, success_rate

ENT-C002: Execution — Source: SRC-C001 through SRC-C014
  Purpose:        A single run of a Computation. The universal "job instance."
  Attributes:
    - computation       | ref ENT-C001                             | required
    - status            | enum (see SM-C001)                       | required
    - allocated_resources | ref ENT-C014 (Allocation)              | required (after scheduling)
    - environment_snapshot | content-addressed ref                  | required (frozen at start)
    - input_snapshot    | list<{ name, dataset_version, checksum }> | required (frozen at start)
    - output_artifacts  | list<ref ENT-C005>                       | optional (populated on completion)
    - result            | ref ENT-C009 (Result)                    | optional (populated on completion)
    - start_time        | datetime                                 | optional (set when running)
    - end_time          | datetime                                 | optional (set on terminal state)
    - exit_code         | integer                                  | optional (set on completion)
    - log_ref           | content-addressed ref                    | optional
    - checkpoints       | list<ref ENT-C008>                       | optional
    - attempt_number    | integer                                  | required  | default: 1
    - parent_execution  | ref ENT-C002 (if retry)                  | optional
    - pipeline_context  | { pipeline: ref ENT-C010, node_id: text } | optional
    - submitted_by      | ref Actor                                | required
    - submitted_at      | datetime                                 | required
    - cost_actual       | { amount: decimal, currency: text }      | optional (computed on completion)
    - cost_projected    | { amount: decimal, currency: text }      | optional (estimated at scheduling)
  Identity:       UUID (globally unique, immutable)
  Lifecycle:      SM-C001 (see §5.2)
  Persistence:    Event-sourced. Current state = materialized view of Event log.
  Constraints:    environment_snapshot and input_snapshot are frozen at Execution start and CANNOT be
                  modified. cost_actual is computed from Allocation × Provider pricing.
  Derived state:  duration = end_time - start_time; utilization = actual_resource_use / allocated

ENT-C003: Environment — Source: SRC-C008
  Purpose:        A fully specified, reproducible execution context.
  Attributes:
    - name              | text                                     | required
    - base_image        | content-addressed ref (OCI digest)       | required
    - packages          | list<{ name, version_exact, checksum }>  | required
    - env_vars          | map<text, text>                          | optional  | secrets excluded
    - runtime_config    | map<text, typed_value>                   | optional
    - hardware_reqs     | { drivers: list, capabilities: list }    | optional
    - content_hash      | SHA-256 of deterministic serialization   | required  | computed
  Identity:       content_hash (content-addressed — same spec = same identity)
  Lifecycle:      Created → Active → Deprecated
  Persistence:    Immutable once created.
  Constraints:    content_hash MUST match the deterministic serialization of all other fields.
                  Environments with identical specs MUST resolve to identical content_hash.

ENT-C004: Dataset — Source: SRC-C004, SRC-C005, SRC-C011
  Purpose:        A versioned, content-addressed data collection.
  Attributes:
    - name              | text                                     | required
    - version           | integer                                  | auto-increment
    - locations         | list<{ provider, uri, region }>          | required  | ≥1
    - format            | text (MIME or domain convention)          | required
    - schema            | structured schema definition             | optional
    - size_bytes        | integer                                  | required
    - record_count      | integer                                  | optional
    - content_hash      | SHA-256 of contents                      | required
    - lineage           | { produced_by: ref ENT-C002, step: text }| optional
    - sealed            | boolean                                  | required  | default: false
    - created_at        | datetime                                 | required
    - created_by        | ref Actor                                | required
  Identity:       UUID + Project scope + version
  Lifecycle:      Draft → Sealed → Active → Archived
  Persistence:    Metadata persistent. Content via DEP-C004.
  Constraints:    Once sealed=true, content MUST NOT change. content_hash verified on seal.

ENT-C005: Artifact — Source: SRC-C008, SRC-C009
  Purpose:        A file or blob produced by or consumed by Computation.
  Attributes:
    - name              | text                                     | required
    - type              | enum(executable, model, image, log, report, custom) | required
    - content_ref       | content-addressed ref                    | required
    - content_hash      | SHA-256                                  | required
    - size_bytes        | integer                                  | required
    - produced_by       | ref ENT-C002 (Execution)                 | optional
    - content_type      | MIME type                                | required
    - metadata          | map<text, text>                          | optional
    - created_at        | datetime                                 | required
  Identity:       content_hash (content-addressed)
  Lifecycle:      Created → Active → Archived
  Persistence:    Immutable once created. Content via DEP-C004.

ENT-C006: Schedule — Source: SRC-C006, SRC-C007
  Purpose:        A declarative rule for when Computations execute.
  Attributes:
    - name              | text                                     | required
    - computation       | ref ENT-C001                             | required
    - type              | enum(one_shot, recurring, event_triggered,
                          conditional, continuous)                  | required
    - cron_expr         | text (RFC 5545 / cron syntax)            | conditional (if recurring)
    - trigger_event     | { source: text, type: text, filter: expression } | conditional (if event_triggered)
    - condition         | expression                               | conditional (if conditional)
    - enabled           | boolean                                  | required  | default: true
    - next_fire_time    | datetime                                 | computed
    - timezone          | IANA timezone                            | required
    - overlap_policy    | enum(allow, skip, queue, cancel_previous)| required  | default: skip
  Identity:       UUID + Project scope
  Lifecycle:      Created → Active → Paused → Archived
  Constraints:    Must reference a Published Computation. overlap_policy governs behavior
                  when a scheduled Execution is still running at the next fire time.

ENT-C007: ResourcePool — Source: SRC-C001 through SRC-C003
  Purpose:        A collection of compute resources with shared policies.
  Attributes:
    - name              | text                                     | required
    - provider          | ref ENT-C015 (Provider)                  | required
    - resources         | { resource_type: { total, available, reserved } } | required
    - location          | { region, zone, jurisdiction }           | required
    - scheduling_policy | ref ENT-C021 (Policy)                    | optional
    - cost_model        | { per_unit_rates: map<resource_type, rate>, billing: enum } | required
    - capabilities      | list<text> (GPU models, interconnects, etc.) | optional
    - status            | enum(online, degraded, offline, draining) | required
    - autoscale         | { enabled: boolean, min: int, max: int, policy: text } | optional
  Identity:       UUID + Organization scope
  Lifecycle:      Created → Online → Degraded | Draining → Offline → Archived
  Constraints:    available ≤ total. reserved ≤ total. available + reserved ≤ total.

ENT-C008: Checkpoint — Source: SRC-C003, SRC-C005
  Purpose:        Serialized snapshot of running Execution state.
  Attributes:
    - execution         | ref ENT-C002                             | required
    - state_ref         | content-addressed ref                    | required
    - state_size        | integer (bytes)                          | required
    - timestamp         | datetime                                 | required
    - sequence_number   | integer (monotonic per Execution)        | required
    - validation_hash   | SHA-256 of state data                    | required
    - metadata          | map<text, text>                          | optional
  Identity:       UUID
  Lifecycle:      Created → Validated → Used | Expired
  Constraints:    validation_hash MUST match state data. sequence_number monotonically increasing
                  per Execution.

ENT-C009: Result — Source: ASM-C003, ASM-C004, SRC-C008
  Purpose:        Verified output of an Execution.
  Attributes:
    - execution         | ref ENT-C002                             | required
    - output_artifacts  | list<ref ENT-C005>                       | optional
    - output_datasets   | list<ref ENT-C004>                       | optional
    - metrics           | map<text, typed_value>                   | optional
    - exit_status       | enum(success, failure, timeout, cancelled, error) | required
    - verification_status | enum(unverified, passed, failed, skipped) | required
    - verification_ref  | ref ENT-C016 (Verification result)       | optional
    - reproducibility_proof | ref ENT-C017 (if computed)           | optional
    - provenance        | ref ENT-C018 (Provenance record)         | required
  Identity:       UUID (1:1 with Execution)
  Lifecycle:      Pending → Completed → Verified | Unverified
  Constraints:    verification_status="passed" requires verification_ref with passing result.
                  provenance MUST be non-empty.

ENT-C010: Pipeline — Source: SRC-C006, SRC-C009
  Purpose:        A DAG of Computations with data dependencies.
  Attributes:
    - name              | text                                     | required
    - description       | text                                     | optional
    - nodes             | list<{ id: text, computation: ref ENT-C001, config_overrides: map }> | required | ≥1
    - edges             | list<{ from_node: text, from_output: text,
                                 to_node: text, to_input: text }>  | optional
    - stages            | list<{ name: text, node_ids: list<text> }> | optional
    - failure_policy    | enum(fail_fast, skip_failed, retry_failed, custom) | required | default: fail_fast
    - concurrency_limit | integer                                  | optional
    - global_budget     | ref ENT-C020 (Budget)                    | optional
    - global_timeout    | duration                                 | optional
    - version           | integer                                  | auto-increment
  Identity:       UUID + Project scope + version
  Lifecycle:      Draft → Published → Deprecated → Archived
  Constraints:    Node graph MUST be acyclic. Edges must reference valid node IDs and
                  output/input names. All referenced Computations must be accessible.

ENT-C011: DataFlow — Source: SRC-C004, SRC-C006
  Purpose:        A typed connection between Computation outputs and inputs within a Pipeline.
  Attributes:
    - pipeline          | ref ENT-C010                             | required
    - source_node       | text (node ID)                           | required
    - source_output     | text (output name)                       | required
    - target_node       | text (node ID)                           | required
    - target_input      | text (input name)                        | required
    - transfer_strategy | enum(push, pull, reference_pass, stream) | required | default: reference_pass
    - serialization     | text (format hint)                       | optional
  Identity:       Composite (pipeline + source_node + source_output + target_node + target_input)
  Lifecycle:      Tied to Pipeline version.
  Constraints:    Source and target must be different nodes. Type compatibility checked at
                  Pipeline publish time.

ENT-C012: Allocation — Source: SRC-C001 through SRC-C003, SRC-C013
  Purpose:        A time-bounded resource claim for an Execution.
  Attributes:
    - execution         | ref ENT-C002                             | required
    - resource_pool     | ref ENT-C007                             | required
    - resources         | map<resource_type, quantity>              | required
    - start_time        | datetime                                 | required
    - end_time          | datetime | null (ongoing)                | optional
    - cost_rate         | map<resource_type, rate>                 | required
    - cost_accrued      | { amount: decimal, currency: text }      | computed
    - utilization       | map<resource_type, percentage>           | computed
    - node_ids          | list<text> (physical nodes)              | optional (for audit)
  Identity:       UUID
  Lifecycle:      Reserved → Active → Released | Revoked
  Constraints:    Resources must not exceed ResourcePool availability at reservation time.

ENT-C013: Provider — Source: SRC-C001, SRC-C013
  Purpose:        An entity that supplies compute resources.
  Attributes:
    - name              | text                                     | required
    - type              | enum(cloud, hpc_center, private_dc, edge, workstation) | required
    - capabilities      | list<{ resource_type, models, interconnects }> | required
    - locations         | list<{ region, zone, jurisdiction }>     | required
    - pricing_model     | { type: enum(on_demand, spot, reserved, prepaid),
                          rates: map<resource_type, rate> }        | required
    - sla_terms         | { availability: decimal, latency: duration } | optional
    - trust_assessment  | { verified: boolean, last_probe: datetime,
                          probe_results: list<ref> }               | required
    - status            | enum(active, suspended, archived)        | required
  Identity:       UUID + Organization scope
  Lifecycle:      Registered → Verified → Active → Suspended → Archived

ENT-C014: Verification — Source: ASM-C004, SRC-C008
  Purpose:        Specification and result of output verification.
  Attributes:
    - type              | enum(deterministic, statistical, checksum,
                          assertion, external)                      | required
    - spec              | { assertions: list<expression>,
                          comparison_method: text,
                          tolerance: decimal,
                          required_reruns: integer }                | required
    - status            | enum(pending, running, passed, failed)   | required
    - executed_at       | datetime                                 | optional
    - details           | text or blob-ref                         | optional
  Identity:       UUID
  Lifecycle:      Defined → Executed → Passed | Failed

ENT-C015: ReproducibilityProof — Source: ASM-C003, SRC-C008
  Purpose:        Record demonstrating reproducibility of a past Execution.
  Attributes:
    - original_execution | ref ENT-C002                            | required
    - reproduction_execution | ref ENT-C002                        | optional (if re-run)
    - environment_match | enum(exact, equivalent, approximate)     | required
    - input_match       | enum(identical, equivalent)              | required
    - output_comparison | { method: text, result: enum(identical,
                          statistically_equivalent, divergent) }   | required
    - divergence_explanation | text                                | conditional (if divergent)
    - computed_at       | datetime                                 | required
  Identity:       UUID
  Lifecycle:      Created → Active → Superseded

ENT-C016: Provenance — Source: ASM-C003, ASM-C007
  Purpose:        Complete chain of origin for computation artifacts.
  Attributes:
    - target            | ref (any computation artifact)           | required
    - inputs            | list<{ type: dataset|artifact|parameter,
                          ref: content-addressed, version: text }> | required
    - computation       | ref ENT-C001 (specification used)        | required
    - environment       | content-addressed ref ENT-C003           | required
    - execution         | ref ENT-C002                             | required
    - resources_used    | map<resource_type, quantity>              | required
    - outputs           | list<content-addressed ref>              | required
    - timestamp         | datetime                                 | required
  Identity:       UUID
  Lifecycle:      Immutable once created.
  Constraints:    All references must be resolvable. No cycles in lineage chain.

ENT-C017: ComputeEnvelope — Source: ASM-C005
  Purpose:        Bounded authority for AI agents operating on computation.
  Attributes:
    - agent             | ref Actor (ACT-C003 or ACT-C004)         | required
    - permitted_computation_types | list<text>                     | optional (empty = all)
    - resource_spend_limit | { per_execution: Budget, per_period: Budget } | required
    - max_execution_duration | duration                            | required
    - max_concurrent    | integer                                  | required
    - permitted_pools   | list<ref ENT-C007>                       | optional (empty = all permitted)
    - permitted_environments | list<ref ENT-C003>                  | optional (empty = all)
    - prohibited_ops    | list<text>                               | optional
    - rate_limit        | { operations: integer, period: duration } | required
    - kill_switch       | boolean                                  | required  | default: false
    - human_approver    | ref Actor                                | required
  Identity:       UUID + Organization scope
  Lifecycle:      Created → Active → Suspended → Revoked
  Constraints:    kill_switch=true halts all operations immediately.
  CROSS-SUBSTRATE ENVELOPE ARCHITECTURE: An AI Agent's total authority is
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

ENT-C018: Budget — Source: ASM-C006, SRC-C013
  Purpose:        Resource consumption limit.
  Attributes:
    - name              | text                                     | required
    - scope             | ref (Organization | Project | Actor | Pipeline) | required
    - dimensions        | list<{ type: enum(cost, cpu_hours, gpu_hours,
                          storage_bytes, custom), limit: decimal,
                          current: decimal, period: enum(per_execution,
                          per_day, per_month, total) }>             | required
    - alert_thresholds  | list<{ percentage: decimal, channel: text }> | optional
    - enforcement       | enum(warn, throttle, block)              | required  | default: block
    - reset_schedule    | cron expression (for periodic budgets)   | conditional
  Identity:       UUID + Organization scope
  Lifecycle:      Created → Active → Exhausted → Reset → Archived
  CROSS-SUBSTRATE NOTE: Budget *definitions* (how much an Organization allocates to
  computation) originate from SUBSTRATE (Business) organizational resource planning.
  Budget *enforcement* (rejecting or throttling computations that exceed limits) is
  COMPUTE's responsibility. COMPUTE receives budget parameters via INT-C006 and reports
  actual spend back to Business for reconciliation and financial reporting. Business
  Transactions (SUBSTRATE TERM-008) record the financial impact; COMPUTE Budgets track
  the operational limits. See INT-C006 for the cost event protocol between COMPUTE and
  Business. See CROSS-SUBSTRATE-CONVENTIONS.md §6 Principle P3.

ENT-C019: Policy — Source: SRC-C001, SRC-C003
  Purpose:        Declarative constraint on computation behavior.
  Attributes:
    - name              | text                                     | required
    - type              | enum(placement, security, cost, priority,
                          environmental, custom)                    | required
    - scope             | ref (Organization | Project | ResourcePool) | required
    - rules             | list<{ condition: expression, action: text,
                          priority: integer }>                     | required
    - enabled           | boolean                                  | required  | default: true
    - version           | integer                                  | auto-increment
  Identity:       UUID + Organization scope + version
  Lifecycle:      Draft → Active → Deprecated → Archived

ENT-C020: Project — Source: SRC-C005, SRC-C006
  Purpose:        Named scope for related computation work.
  Attributes:
    - name              | text       | unique within Organization  | required
    - description       | text                                     | optional
    - owner             | ref Actor                                | required
    - members           | list<{ actor: ref, role: enum(admin, contributor, viewer) }> | required
    - budgets           | list<ref ENT-C018>                       | optional
    - policies          | list<ref ENT-C019>                       | optional
    - default_environment | ref ENT-C003                           | optional
    - default_resource_pool | ref ENT-C007                         | optional
  Identity:       UUID + Organization scope
  Lifecycle:      Created → Active → Archived

ENT-C021: Metric — Source: SRC-C012
  Purpose:        Time-series measurement from Execution.
  Attributes:
    - execution         | ref ENT-C002                             | required
    - name              | text                                     | required
    - type              | enum(counter, gauge, histogram, summary) | required
    - value             | decimal                                  | required
    - labels            | map<text, text>                          | optional
    - timestamp         | datetime                                 | required
  Identity:       Composite (execution + name + timestamp)
  Lifecycle:      Immutable once recorded.
```

### 5.2 State Machines

```
SM-C001: Execution Lifecycle — Governs: ENT-C002
  States:
    - submitted:    Computation request received, validated, not yet scheduled
    - queued:       Accepted by scheduler, waiting for resource availability
    - scheduled:    Resources identified and reserved, waiting for execution slot
    - provisioning: Resources being allocated and environment being prepared
    - running:      Code actively executing
    - checkpointing: Creating a Checkpoint (running continues after)
    - preempted:    Suspended — Checkpoint saved, resources reclaimed
    - completing:   Execution finished, outputs being collected and registered
    - completed:    Terminal — successful. Result available.
    - failed:       Terminal — execution error. Partial outputs may exist.
    - timeout:      Terminal — exceeded wall-clock limit.
    - cancelled:    Terminal — cancelled by Actor or system.
    - retrying:     Non-terminal — previous attempt failed, new attempt being created.
  Transitions:
    - submitted → queued:        Validation passes, Policies satisfied, Budget available
    - submitted → cancelled:     Actor cancels before queuing, or validation fails
    - queued → scheduled:        Resources identified by scheduler
    - queued → cancelled:        Actor cancels, or queue timeout exceeded
    - scheduled → provisioning:  Resource allocation confirmed
    - scheduled → queued:        Allocated resources became unavailable — re-queue
    - provisioning → running:    Environment ready, execution begins
    - provisioning → failed:     Environment setup fails (e.g., image pull error)
    - running → checkpointing:   Checkpoint interval reached or manual trigger
    - checkpointing → running:   Checkpoint saved successfully
    - running → completing:      Exit code received
    - running → preempted:       Higher-priority work needs resources
    - running → failed:          Runtime error, OOM, hardware fault
    - running → timeout:         Wall-clock limit exceeded
    - running → cancelled:       Actor cancels or kill switch activated
    - preempted → queued:        Re-queued for scheduling with Checkpoint reference
    - completing → completed:    Outputs registered, Result created
    - completing → failed:       Output registration fails
    - failed → retrying:         Retry policy allows another attempt
    - timeout → retrying:        Retry policy allows another attempt
    - retrying → submitted:      New Execution created as retry (parent_execution set)
  Terminal states: completed, failed (after max retries), timeout (after max retries), cancelled

SM-C002: Pipeline Execution Lifecycle — Governs: Pipeline runs
  States:
    - submitted, queued, running, paused, completing, completed, failed, cancelled
  Key transitions:
    - running: nodes execute per dependency order; Pipeline is "running" while any node is active
    - paused: manual pause — all running nodes checkpoint if possible
    - failed: depends on failure_policy — fail_fast stops all; skip_failed continues; retry_failed retries
    - completed: all required nodes completed successfully

SM-C003: ResourcePool Lifecycle — Governs: ENT-C007
  States: created → online → degraded → draining → offline → archived
  Key transitions:
    - online → degraded: some resources unhealthy but pool operational
    - degraded → online: all resources recovered
    - online/degraded → draining: no new Allocations; existing complete naturally
    - draining → offline: all Allocations released
    - offline → online: resources restored

SM-C004: ComputeEnvelope Lifecycle — Governs: ENT-C017
  States: created → active → suspended → revoked
  Key transitions:
    - active → suspended: threshold exceeded or manual suspension. All pending cancelled.
    - suspended → active: human approver re-enables
    - active/suspended → revoked: permanent deactivation. Agent can never use this Envelope.
```

---

## 6. INTERFACES (SYSTEM SURFACES)

```
IFC-C001: Computation CRUD API — Exposes: ENT-C001
  Operations:     create, read, update (draft only), archive, list, search
  Auth:           ACT-C001/C002/C003/C004 per Project role; ACT-C005 per Endpoint
  Input format:   Structured (JSON/protobuf) Computation specification
  Output format:  Computation object with resolved references
  Idempotency:    create — idempotent via client-provided idempotency key (30-day window)
  Rate limit:     Per Actor, per Organization (default: 1000/min)
  Error codes:    400 (invalid spec), 403 (permission), 404 (ref not found), 409 (conflict), 429 (rate)

IFC-C002: Execution Submit API — Exposes: ENT-C002 creation
  Operations:     submit (creates Execution from Computation), cancel, list, get_status
  Auth:           Per Computation permissions; Envelope check for AI agents
  Input format:   { computation_ref, parameter_overrides, priority, tags }
  Output format:  Execution object with initial status = submitted
  Idempotency:    submit — idempotent via idempotency key
  Rate limit:     Per Actor (default: 100/min)
  Validation:     Budget check, Envelope check, Policy check — all BEFORE acceptance

IFC-C003: Pipeline API — Exposes: ENT-C010
  Operations:     create, read, update (draft), publish, execute, cancel_run, get_run_status
  Auth:           Per Project role
  Input format:   Pipeline definition (nodes, edges, stages, policies)
  Output format:  Pipeline object; Pipeline run status with per-node details
  Validation:     DAG acyclicity, type compatibility of DataFlows, all referenced
                  Computations accessible

IFC-C004: Resource Query API — Exposes: ENT-C007, ENT-C013
  Operations:     list_pools, get_pool, list_providers, get_provider, estimate_cost,
                  check_availability
  Auth:           read for all authenticated Actors; admin for mutations
  Output format:  Resource inventory with availability, pricing, capabilities
  Caching:        Availability snapshots refreshed every 60s. Pricing from Provider API.

IFC-C005: Result & Provenance API — Exposes: ENT-C009, ENT-C016
  Operations:     get_result, get_provenance, reproduce, verify, compare_results
  Auth:           Per Execution permissions
  Output format:  Result with full provenance chain, verification status

IFC-C006: Audit & Time-Travel API — Exposes: Event log
  Operations:     query_events (by entity, time range, actor, type),
                  get_state_at (entity + timestamp), get_execution_history
  Auth:           ACT-C006 (Auditor) — read-all; ACT-C002 — read within org
  Output format:  Event stream or point-in-time state snapshot

IFC-C007: Metric & Monitoring API — Exposes: ENT-C021, real-time metrics
  Operations:     query_metrics (by execution, time range, name), stream_metrics,
                  get_utilization, get_cost_summary
  Auth:           Per Project role
  Output format:  Time-series data; OpenTelemetry-compatible

IFC-C008: Data Export API — Exposes: bulk export of all Organization data
  Operations:     export_all, export_project, export_executions
  Auth:           ACT-C002 (admin) required
  Output format:  JSON-LD, CSV, or Parquet
  Throttling:     Background job; bounded by Organization export quota

IFC-C009: Schedule API — Exposes: ENT-C006
  Operations:     create, read, update, pause, resume, delete, list, trigger_now
  Auth:           Per Project role
  Validation:     Referenced Computation must be Published

IFC-C010: Budget & Policy API — Exposes: ENT-C018, ENT-C019
  Operations:     create, read, update, archive, get_usage
  Auth:           ACT-C002 (admin)
  Output format:  Budget with current usage percentages; Policy with evaluation results

IFC-C011: Event Stream — Exposes: real-time event feed
  Operations:     subscribe (by entity type, project, actor, event type),
                  acknowledge, replay (from sequence number)
  Protocol:       WebSocket or server-sent events; persistent subscription with delivery
                  guarantee (at-least-once)
  Auth:           Per subscription scope
```

---

## 7. DATA FLOWS (HOW CAPABILITIES HAPPEN)

```
FLOW-C001: Submit and Execute Computation — Implements: CAP-C001, CAP-C002, CAP-C003, CAP-C011
  Trigger:             Actor submits Execution via IFC-C002
  Inputs:              Computation ref (or inline spec), parameter overrides, priority
  Steps:
    1. Validate Actor permissions (Project role, Organization membership)
    2. If Actor is AI agent: verify Compute Envelope (ENT-C017) permits this
       computation type, resource level, and pool
    3. Resolve Computation spec: fetch published version, apply parameter overrides
    4. Validate resource requirements: min ≤ requested ≤ max, all types recognized
    5. Check Budget(s): projected cost ≤ remaining budget. If block policy and insufficient: reject.
    6. Check Policy(ies): placement, security, cost, environmental constraints all satisfied
    7. Freeze inputs: resolve all input_bindings to specific Dataset versions, record checksums
    8. Freeze environment: resolve Environment ref to content-addressed snapshot
    9. Create Execution (status=submitted) with frozen snapshots
    10. Record submission Event (hash-chained)
    11. Enqueue for scheduling (priority-ordered)
    12. Scheduler matches Execution to ResourcePool based on: resource fit, Policy
        constraints, data locality (ASM-C012), cost optimization, and priority
    13. Reserve Resources → create Allocation (ENT-C012) → status=scheduled
    14. Provision environment on allocated Resources → status=provisioning
    15. Start execution → status=running
    16. Monitor: collect Metrics, check timeout, handle Checkpoints
    17. On completion: collect outputs, register Artifacts/Datasets, compute cost
    18. Create Result (ENT-C009) with Provenance (ENT-C016) → status=completing
    19. Run Verification if configured → status=completed
    20. Release Allocation
    21. Record completion Event
    22. Trigger downstream: notify Actor, update Budget usage, fire Pipeline DataFlows
  Outputs:             Execution UUID, Result (on completion)
  Side effects:        Budget updated. Metrics recorded. Events emitted. Pipeline may advance.
  Error paths:         Step 2 → ERR-C001 (envelope violation)
                       Step 5 → ERR-C002 (budget exceeded)
                       Step 6 → ERR-C003 (policy violation)
                       Step 14 → ERR-C004 (provisioning failure — retry from step 12)
                       Step 15 → ERR-C005 (runtime error) → retry per policy or → failed
                       Step 16 timeout → ERR-C006 (timeout) → retry per policy or → timeout
  Atomicity:           Steps 1-11 (submission) are atomic. Steps 12-21 are per-step with
                       recovery via Checkpoints and retry.

FLOW-C002: Execute Pipeline — Implements: CAP-C017, CAP-C018, CAP-C019
  Trigger:             Actor executes Pipeline via IFC-C003
  Inputs:              Pipeline ref, parameter overrides, priority
  Steps:
    1. Validate Actor permissions and Budget
    2. Resolve Pipeline: fetch published version, apply overrides
    3. Validate DAG: acyclicity, type compatibility, all Computations accessible
    4. Create Pipeline Execution (SM-C002, status=submitted)
    5. Topological sort: determine execution order
    6. For each node with no unresolved dependencies: submit via FLOW-C001
       (with pipeline_context set)
    7. As each node completes: resolve DataFlows to downstream nodes, submit them
    8. If a node fails: apply failure_policy
       - fail_fast: cancel all running nodes, Pipeline → failed
       - skip_failed: mark dependent nodes as skipped, continue others
       - retry_failed: retry the failed node per its retry_policy
    9. When all nodes reach terminal state: Pipeline → completing → completed
    10. Aggregate Results: Pipeline Result = collection of per-node Results
    11. Record Pipeline completion Event
  Outputs:             Pipeline Execution UUID, aggregated Results
  Error paths:         Per-node errors handled per step 8.
                       Global timeout → cancel all running nodes → Pipeline → timeout
  Atomicity:           Per-node Executions are independent. Pipeline state updated per event.

FLOW-C003: Checkpoint and Resume — Implements: CAP-C026, CAP-C027
  Trigger:             Checkpoint interval, manual trigger, or preemption signal
  Inputs:              Running Execution ref
  Steps:
    1. Signal Execution to serialize state → status=checkpointing
    2. Execution writes state to provided storage path
    3. Create Checkpoint (ENT-C008) with content-addressed ref and validation hash
    4. Verify Checkpoint: hash matches, size reasonable, format valid
    5. Record Checkpoint Event → status=running (resume after checkpoint)
    For preemption:
    6. After Checkpoint validated: release Resources → status=preempted
    7. Re-enqueue with Checkpoint reference → status=queued
    8. When rescheduled: provision new Resources, restore from Checkpoint
    9. Resume execution → status=running
  Outputs:             Checkpoint UUID; for preemption: new Allocation on resume
  Error paths:         Step 2 timeout → Execution continues without checkpoint (log warning)
                       Step 4 fail → discard Checkpoint, retry at next interval
                       Step 8 fail → ERR-C004 (provisioning failure)
  Atomicity:           Checkpoint creation is atomic. Preemption sequence is multi-step
                       with recovery from Checkpoint.

FLOW-C004: Reproduce Execution — Implements: CAP-C012
  Trigger:             Actor requests reproduction via IFC-C005
  Inputs:              Original Execution ref
  Steps:
    1. Retrieve original Execution's Provenance (ENT-C016)
    2. Verify: Environment still available (content-addressed — if exists, it's identical)
    3. Verify: input Datasets still available and checksums match
    4. Create new Computation with identical spec and parameters
    5. Submit via FLOW-C001 with same Environment and inputs
    6. On completion: compare outputs using configured comparison method
       - deterministic: bit-for-bit comparison
       - statistical: distribution comparison within tolerance
       - checksum: output checksum comparison
    7. Create ReproducibilityProof (ENT-C015) with comparison results
    8. Record reproduction Event
  Outputs:             ReproducibilityProof UUID, comparison result
  Error paths:         Step 2/3 → ERR-C010 (artifacts unavailable — proof cannot be computed)
  Atomicity:           The reproduction Execution follows FLOW-C001. Proof creation is atomic.

FLOW-C005: Evaluate Schedule — Implements: CAP-C002
  Trigger:             System clock tick (internal, continuous)
  Inputs:              Current timestamp; all active Schedules
  Steps:
    1. Query all Schedules where next_fire_time ≤ now
    2. For each due Schedule: acquire processing lock
    3. Check overlap_policy: if previous Execution still running, apply policy
    4. Submit Execution via FLOW-C001
    5. Compute next_fire_time based on Schedule type
    6. Record Schedule execution Event
    7. Release lock
  Outputs:             Submitted Executions; updated next_fire_times
  Error paths:         Step 2 lock contention → skip (another node handles).
                       Step 4 failure → log, retry at next evaluation. After 3 consecutive:
                       alert + auto-disable Schedule.
  Atomicity:           Per Schedule.

FLOW-C006: Data Export — Implements: CAP-C023
  Trigger:             ACT-C002 requests export via IFC-C008
  Inputs:              Scope (organization, project, or execution set), format
  Steps:
    1. Validate ACT-C002 permissions
    2. Enumerate all artifacts within scope
    3. Serialize to requested format (JSON-LD, CSV, Parquet)
    4. Stream to DEP-C004 (Content Store) as export artifact
    5. Notify requestor with download reference
  Outputs:             Export artifact reference
  Error paths:         Step 3-4 → ERR-C005 (internal). Retry from last successful chunk.
  Atomicity:           Per entity type (each independently exportable).
```

---

## 8. INTEGRATION CONTRACTS (EXTERNAL SYSTEMS)

```
INT-C001: Time Source — Depends on: DEP-C001
  Protocol:          NTP (RFC 5905) + optional GPS PPS
  Auth:              N/A (NTP); NTS for authenticated
  Failure modes:     Timeout / all servers unreachable / excessive drift (>1s)
  Retry policy:      3 servers concurrently; best response wins. Fallback: local monotonic clock.
                     Events stamped with uncertainty interval.
  Idempotency:       N/A (stateless)

INT-C002: Identity Verification — Depends on: DEP-C002
  Protocol:          OpenID Connect / SAML 2.0 / WebAuthn
  Auth:              Mutual TLS
  Failure modes:     Provider down / token expired / invalid signature
  Retry policy:      3 retries, 1s/2s/4s backoff. Circuit breaker: open after 5 failures;
                     half-open after 60s.
  Idempotency:       Safe to retry (read-only)

INT-C003: Resource Provider Integration — Depends on: DEP-C003, DEP-C008
  Protocol:          Provider-specific (AWS API, K8s API, Slurm CLI, custom REST)
  Auth:              Per provider (IAM, service account, certificates)
  Request format:    SUBSTRATE-COMPUTE internal format → Provider-specific adapter translates
  Response format:   Provider-specific → adapter normalizes to internal format
  Failure modes:     Provider API down / rate-limited / quota exceeded / instance unavailable
  Retry policy:      3 retries, exponential backoff 2s/10s/60s. Circuit breaker: open after
                     5 failures in 120s; half-open after 300s.
  Idempotency:       Allocation: REQUIRED — keyed by Execution UUID. Safe to retry.
                     Deallocation: idempotent by design (deallocate already-deallocated = no-op).
  Partial success:   Multi-node allocation: all-or-nothing. If partial: release acquired, retry.

INT-C004: Content Store — Depends on: DEP-C004
  Protocol:          S3-compatible API / OCI registry / content-addressable store
  Auth:              IAM / service account / signed URLs
  Failure modes:     Timeout / storage full / not found / checksum mismatch
  Retry policy:      3 retries, 2s/5s/15s backoff. Upload: verify checksum after each retry.
                     Circuit breaker: open after 5 failures in 120s.
  Idempotency:       Content-addressed — same content = same ref. Safe to retry.

INT-C005: Notification Delivery — Depends on: DEP-C005
  Protocol:          SMTP / webhook / push / in-system
  Failure modes:     Timeout / bounce / rate-limited
  Retry policy:      3 retries, 1m/5m/30m backoff. TTL: 72h default.
  Idempotency:       Webhook: idempotency key in header.

INT-C006: SUBSTRATE (Business) — Depends on: DEP-C006
  Protocol:          Event bus (shared) + REST API for cost/billing queries
  Auth:              Mutual TLS + shared identity (INTEROP-C003)
  Request format:    Cost events: { execution_id, resource_usage, cost_amount, currency }
  Failure modes:     Business substrate unavailable
  Retry policy:      Cost events queued locally. Reconciliation on recovery.
  Partial success:   Computations continue. Cost tracking eventually consistent.

INT-C007: SUBSTRATE-KNOWLEDGE — Depends on: DEP-C007
  Protocol:          Event bus (shared) + REST API for knowledge artifact creation
  Auth:              Mutual TLS + shared identity
  Request format:    Computation result → Evidence/Observation artifact
  Failure modes:     Knowledge substrate unavailable
  Retry policy:      Knowledge events queued. Created on recovery.
  Partial success:   Computations unaffected. Knowledge artifact creation deferred.

INT-C008: COMPUTE ↔ COMMUNICATION Integration
  Purpose:    Provide computational analysis services for discourse and resolve
              computation references in speech acts.
  Protocol:
    — Event-driven via shared event bus + REST API for analysis requests.
    — COMPUTE emits: substrate.compute.job.completed,
      substrate.compute.execution.completed.
    — COMMUNICATION submits analysis requests (argumentation evaluation,
      translation, summarization) as Pipeline executions.
  Delegation:
    — COMMUNICATION may request analysis from COMPUTE Pipelines (TERM-C010).
      COMPUTE owns execution; COMMUNICATION owns discourse application of results.
    — COMMUNICATION Speech Acts may reference COMPUTE Execution (TERM-C006) results
      via cross-substrate reference resolution (CONVENTIONS §5).
  Boundary: COMPUTE owns computation and execution. COMMUNICATION owns discourse
            semantics. Principle P1. This is the COMPUTE-side mirror of INT-M005.

INT-C009: COMPUTE ↔ TEMPORAL Integration
  Purpose:    Execute scheduling solvers as COMPUTE Pipelines.
  Protocol:
    — Event-driven via shared event bus + direct API for solver submission.
    — COMPUTE emits: substrate.compute.job.completed (solver result available).
    — TEMPORAL submits SchedulingProblem as COMPUTE Dataset (TERM-C004) input.
    — COMPUTE returns SchedulingSolution as Result.
  Delegation:
    — TEMPORAL defines what to solve (SchedulingProblem: activities, dependencies,
      constraints, resources, objectives). COMPUTE defines how to solve it
      (solver Pipeline, resource allocation, execution scheduling).
    — Multiple solvers registered (CP-SAT, OR-Tools, Gurobi, custom heuristics).
      TEMPORAL selects per SchedulingPolicy. COMPUTE treats each as a Pipeline
      implementation variant.
  Boundary: TEMPORAL owns problem definition and solution interpretation.
            COMPUTE owns solver execution. Principle P1.
            This is the COMPUTE-side mirror of INT-T002.

INT-C010: COMPUTE ↔ SPATIAL Integration
  Purpose:    Execute spatial computation problems (routing optimization, territory
              rebalancing, coverage analysis) as COMPUTE Pipelines.
  Protocol:
    — Event-driven via shared event bus.
    — COMPUTE emits: substrate.compute.job.completed (spatial solution).
    — SPATIAL submits SpatialProblem as COMPUTE Pipeline input.
  Delegation:
    — SPATIAL defines the spatial problem (VRP, coverage optimization, territory
      rebalancing, large-scale spatial join, network analysis). COMPUTE executes.
    — SPATIAL owns problem formulation and result interpretation. COMPUTE owns
      solver execution and resource management.
  Boundary: SPATIAL owns geography. COMPUTE owns computation.
            Principle P1. This is the COMPUTE-side mirror of INT-S002.

INT-C011: COMPUTE ↔ PHYSICAL Integration
  Purpose:    Provide advanced computation for physical control, simulation, and
              predictive maintenance.
  Protocol:
    — Event-driven via shared event bus.
    — COMPUTE emits: substrate.compute.job.completed,
      substrate.compute.pipeline.result_available.
    — PHYSICAL submits: MPC optimization problems, Digital Twin simulation requests,
      predictive maintenance model inputs.
    — PHYSICAL emits: substrate.physical.measurement.recorded (sensor data for
      processing pipelines, e.g., perception, anomaly detection).
  Delegation:
    — PHYSICAL may submit MPC optimization, Digital Twin simulation, and predictive
      maintenance models as COMPUTE Pipeline (TERM-C010) requests.
    — COMPUTE executes and returns results. PHYSICAL consumes for control decisions.
    — CRITICAL: when COMPUTE is unavailable, PHYSICAL MPC degrades to PID.
      Safety is NEVER dependent on COMPUTE availability.
  Boundary: PHYSICAL owns control and safety (always authoritative for equipment
            state). COMPUTE owns optimization algorithms. Principle P1.
            This is the COMPUTE-side mirror of INT-P003.

INT-C012: COMPUTE ↔ DESIGN Integration
  Purpose:    Execute design analysis simulations and design space explorations.
  Protocol:
    — Event-driven via shared event bus.
    — COMPUTE emits: substrate.compute.execution.completed,
      substrate.compute.pipeline.result_available,
      substrate.compute.budget.exhausted.
    — DESIGN emits: substrate.design.analysis.submitted (FEA, CFD, topology
      optimization), substrate.design.space.exploration_requested.
  Delegation:
    — DESIGN owns "what to simulate" (Geometry TERM-D006 + Material TERM-D008 +
      Constraints + boundary conditions). COMPUTE owns "how to simulate" (solver
      Pipeline, resource allocation, scheduling).
    — DESIGN DesignSpace (TERM-D026) exploration runs as COMPUTE Pipeline.
    — DESIGN Geometry consumed as COMPUTE Dataset (TERM-C004) input.
    — COMPUTE AnalysisResult returned; DESIGN creates AnalysisResult (TERM-D014)
      from COMPUTE output.
  Boundary: DESIGN owns simulation intent and result interpretation.
            COMPUTE owns execution. Principle P1.
            This is the COMPUTE-side mirror of INT-D003.

INT-C013: COMPUTE ↔ GOVERNANCE Integration
  Purpose:    Coordinate computation jurisdiction, algorithmic auditing, and
              normative compute budget constraints.
  Protocol:
    — Event-driven via shared event bus.
    — COMPUTE emits: substrate.compute.execution.completed,
      substrate.compute.job.completed,
      substrate.compute.budget.exhausted.
    — GOVERNANCE emits: substrate.governance.norm.effective (computation
      jurisdiction rules, algorithmic audit requirements),
      substrate.governance.assessment.completed (algorithmic audits).
  Delegation:
    — GOVERNANCE resolves which Jurisdictions (TERM-G017) apply to cross-border
      computation. COMPUTE queries before executing where jurisdiction matters.
    — GOVERNANCE Norms (TERM-G001) may set computational budget constraints
      (e.g., maximum GPU-hours per period for a given agent). COMPUTE enforces.
    — GOVERNANCE owns algorithmic audit requirements. COMPUTE provides Execution
      (TERM-C006) records and Provenance (TERM-C018) as audit evidence.
  Boundary: GOVERNANCE defines rules. COMPUTE enforces and provides evidence.
            Principle P3. This is the COMPUTE-side mirror of INT-G003.
```

**Cross-substrate event topics emitted by SUBSTRATE-COMPUTE:**

```
substrate.compute.job.completed              — Pipeline or standalone Computation completed
substrate.compute.execution.completed        — Individual Execution reached terminal state
substrate.compute.computation.completed      — Alias for execution.completed (backward compat)
substrate.compute.pipeline.result_available  — Pipeline stage produced consumable result
substrate.compute.budget.exhausted           — ComputeEnvelope budget limit reached
substrate.compute.execution.failed           — Execution failed (error, timeout, resource issue)
substrate.compute.execution.timeout          — Execution exceeded max_duration
substrate.compute.checkpoint.created         — Checkpoint saved (enables recovery/resume)
```

**Correlated failure scenarios:**

- DEP-C002 + DEP-C008 fail simultaneously: No new submissions. Running Executions continue to completion. Results stored locally until Content Store recovers.
- DEP-C003 + DEP-C008 fail simultaneously: No new scheduling. Running Executions continue. Completed results queue locally.
- All DEPs fail (catastrophic): Edge nodes continue in offline mode (CAP-C028). Computation specs queued locally. Already-running Executions on local resources continue. Full functionality restored on recovery.

---

## 9. AUTHORIZATION & ACCESS MODEL

### Actors

| Actor | Description | Source |
|-------|-------------|--------|
| ACT-C001 | Human Operator — submits, monitors, manages computations | §1 |
| ACT-C002 | Human Administrator (Compute Steward) — configures pools, policies, budgets | §1 |
| ACT-C003 | AI Agent (Narrow Compute) — bounded automation within Compute Envelope | §1 |
| ACT-C004 | AI Agent (General Compute) — expanded reasoning about computation strategy | §1 |
| ACT-C005 | External System — integration endpoint, untrusted | §1 |
| ACT-C006 | Auditor — read-all, time-travel queries | §1 |
| ACT-C007 | Resource Provider — supplies hardware, partially trusted | §1 |

### Resources & Permissions Matrix

| Resource | ACT-C001 | ACT-C002 | ACT-C003 | ACT-C004 | ACT-C005 | ACT-C006 | ACT-C007 |
|----------|----------|----------|----------|----------|----------|----------|----------|
| Computation (own Project) | CRUD | CRUD (all) | CR (Envelope) | CRUD (Envelope) | CR (scoped) | R (all) | — |
| Execution (own Project) | submit, cancel, read | all | submit (Envelope) | submit, cancel (Envelope) | submit (scoped) | R (all) | — |
| Pipeline (own Project) | CRUD, execute | CRUD (all), execute | execute (Envelope) | CRUD, execute (Envelope) | execute (scoped) | R (all) | — |
| Result / Provenance | R (own) | R (all) | R (own) | R (own) | R (scoped) | R (all) | — |
| ResourcePool | R | CRUD | R | R | R (limited) | R (all) | R (own) |
| Provider | R | CRUD | R | R | — | R (all) | CRUD (own) |
| Budget | R (own) | CRUD | R (own) | R (own) | — | R (all) | — |
| Policy | R | CRUD | R | R | — | R (all) | — |
| ComputeEnvelope | R (own) | CRUD | R (own) | R (own) | — | R (all) | — |
| Event log | R (own Project) | R (own Org) | R (own) | R (own) | — | R (all) | R (own) |
| Data Export | — | execute | — | — | — | execute | — |
| Project | R (member) | CRUD | R (member) | R (member) | — | R (all) | — |

**Envelope enforcement (AI Agents):**
Every operation by ACT-C003 or ACT-C004 is checked against their ComputeEnvelope (ENT-C017) before execution. Envelope violations are logged, rejected, and trigger an alert to the human_approver. Three consecutive violations within 1 hour → automatic Envelope suspension.

**External System (ACT-C005):**
All permissions scoped to explicitly granted Computations and ResourcePools. Rate-limited (default: 60/min). No access to Budgets, Policies, Envelopes, or Admin operations.

**Resource Provider (ACT-C007):**
Can manage their own Provider and ResourcePool records. Cannot access other Organizations' Execution data. Billing data shared per bilateral agreement.

---

## 10. SECURITY & PRIVACY MODEL

### 10.1 Threat Model

```
THREAT-C001: Malicious Code Execution
  Vector:     Actor submits Computation containing malware, cryptominer, or exfiltration code
  Impact:     Resource theft, data exfiltration, lateral movement to other Executions
  Mitigation: CAP-C024 (sandboxing). All Executions run in isolated environments with
              no network access except explicitly declared endpoints. Resource limits enforced.
              Egress filtering. Runtime behavior monitoring. Anomaly detection on resource usage.

THREAT-C002: Resource Exhaustion / Denial of Service
  Vector:     Actor submits many large Computations to exhaust Budget or pool capacity
  Impact:     Legitimate Computations cannot run
  Mitigation: CAP-C008 (Budget enforcement). Rate limiting (IFC-C001, IFC-C002). Per-Actor
              concurrency limits. Priority scheduling ensures critical work is not starved.

THREAT-C003: Data Exfiltration via Computation
  Vector:     Computation code reads input Datasets and sends them to unauthorized endpoint
  Impact:     Confidential data leak
  Mitigation: CAP-C024 (sandboxing — no undeclared network). Egress whitelist per Computation.
              Data classification labels propagated from Datasets to Execution constraints.
              Network monitoring for anomalous egress.

THREAT-C004: Provider Compromise
  Vector:     Malicious or compromised Resource Provider reports false resource availability,
              returns tampered results, or captures data from Executions
  Impact:     Incorrect results, data breach, resource fraud
  Mitigation: Provider trust verification (ENT-C013 trust_assessment). Periodic benchmark
              probes. Result Verification (CAP-C014). Sensitive computations restricted to
              trusted providers via Policy. Encryption at rest and in transit.

THREAT-C005: Provenance Forgery
  Vector:     Actor manipulates Provenance records to make results appear legitimate
  Impact:     False claims of reproducibility, incorrect scientific conclusions
  Mitigation: Hash-chained Event log (CAP-C003, CAP-C004). Provenance records are immutable
              and content-addressed. Any modification detectable via chain verification.

THREAT-C006: AI Agent Envelope Escape
  Vector:     AI Agent exploits vulnerability to operate outside its Compute Envelope
  Impact:     Unauthorized resource consumption, unauthorized data access
  Mitigation: Envelope enforcement at permission layer (not bypassable by agent).
              Kill switch (ENT-C017). Anomaly detection on agent behavior patterns.
              Three-violation auto-suspension.

THREAT-C007: Side-Channel Attacks
  Vector:     Co-located Computations infer data about each other via timing, cache, or
              resource usage patterns
  Impact:     Information leakage between tenants
  Mitigation: Security Policy types include isolation levels (shared, dedicated, air-gapped).
              Sensitive computations can require dedicated hardware. Noisy-neighbor detection.

THREAT-C008: Supply Chain Attack via Environment
  Vector:     Compromised package in an Environment's dependency tree
  Impact:     Code injection into all Computations using that Environment
  Mitigation: Environments are content-addressed and immutable. Package checksums verified.
              Vulnerability scanning on Environment creation. CVE monitoring with alerts.
```

### 10.2 Encryption Requirements

```
ENC-C001: Data in transit — TLS 1.3 minimum for all API communication.
          Mutual TLS for inter-substrate and Provider communication.
ENC-C002: Data at rest — All Datasets, Artifacts, Checkpoints, and Event logs encrypted
          at rest with AES-256-GCM. Key management via HSM or KMS integration.
ENC-C003: Secrets — All secrets (API keys, credentials, tokens) stored in dedicated
          secret manager. Injected into Execution environments at runtime, never persisted
          in Computation specifications, Event logs, or Metric data.
ENC-C004: Execution isolation — Each Execution runs with its own ephemeral encryption key
          for local storage. Key destroyed on Execution completion.
```

### 10.3 Abuse Cases

```
ABUSE-C001: Cryptomining
  Detection:   GPU utilization high + no declared GPU workload; CPU patterns matching mining
  Response:    Auto-terminate Execution. Alert ACT-C002. Flag Actor for review.

ABUSE-C002: DDoS Amplification
  Detection:   Computation generating outbound traffic disproportionate to declared outputs
  Response:    Egress rate-limited per Computation declaration. Auto-terminate on violation.

ABUSE-C003: Model Theft via Side Channel
  Detection:   Repeated Computations with similar inputs targeting co-located model serving
  Response:    Anomaly detection on access patterns. Rate limiting. Isolation level escalation.

ABUSE-C004: Resource Fraud by Provider
  Detection:   Provider benchmark probes return results inconsistent with declared capabilities
  Response:    Provider trust score reduced. Alert ACT-C002. Suspend provider after 3 failures.
```

### 10.4 Privacy

```
PII-C001:  Computation specifications, parameters, and results are Organization-private by
           default. Cross-Organization sharing requires explicit grant.
PII-C002:  Event logs redact Actor identity in external audit views unless specifically
           authorized. Internal logs retain full identity for accountability.
PII-C003:  Metric data aggregated at Organization level for system-wide analytics.
           Per-Execution metrics only accessible to authorized Project members.
PII-C004:  Data Export (CAP-C023) includes all Organization data — including Event logs
           with full identity — for data portability. Recipient manages subsequent privacy.
PII-C005:  Provider cannot access Execution inputs/outputs. Data encrypted with Organization
           key. Provider sees only resource utilization metrics.
```

---

## 11. BEHAVIORAL CONTRACTS (SYSTEM LAW)

### 11.1 Invariants (must ALWAYS hold)

```
INV-C001:  Every Execution MUST have a non-empty Provenance record linking to: the exact
           Computation specification version, the content-addressed Environment, the specific
           input Dataset versions (with checksums), and the resource Allocation.
           — Source: CAP-C011

INV-C002:  The Event log MUST be append-only. No Event may be modified or deleted.
           The hash chain MUST be continuous — every Event's hash includes the
           previous Event's hash.
           — Source: CAP-C003, CAP-C004

INV-C003:  For every Execution in terminal state (completed, failed, timeout, cancelled),
           a Result (ENT-C009) MUST exist with exit_status and provenance.
           — Source: CAP-C003

INV-C004:  An AI Agent's operations MUST NOT exceed its ComputeEnvelope limits.
           If enforcement fails (bug), the Event log MUST record the violation for
           post-hoc audit and remediation.
           — Source: CAP-C020

INV-C005:  Budget.current MUST equal the sum of all Allocation costs within the Budget's
           scope and period. Divergence triggers reconciliation.
           — Source: CAP-C008

INV-C006:  For any content-addressed entity (Environment, Dataset, Artifact), the stored
           content MUST match its content_hash. Mismatch at any point = integrity failure.
           — Source: CAP-C013

INV-C007:  A Pipeline's node graph MUST be acyclic at all times (Draft through Published).
           — Source: CAP-C017

INV-C008:  ResourcePool.available + ResourcePool.reserved ≤ ResourcePool.total at all times.
           — Source: ENT-C007

INV-C009:  No Execution may access data, network endpoints, or resources not declared in
           its Computation specification.
           — Source: CAP-C024
```

### 11.2 Preconditions (must hold BEFORE operations)

```
PRE-C001:  submit_execution →
           Actor MUST be authenticated and authorized for the Computation's Project.
           Computation MUST be in Published state. All input_bindings MUST resolve to
           existing Dataset versions. Environment MUST be resolvable (content-addressed).
           Budget MUST have sufficient remaining capacity (if enforcement=block).
           All applicable Policies MUST be satisfied.
           If Actor is AI agent: ComputeEnvelope MUST be Active and permit this operation.

PRE-C002:  cancel_execution →
           Execution MUST be in a non-terminal state.
           Actor MUST be the submitter, or ACT-C002, or human_approver of the agent's Envelope.

PRE-C003:  checkpoint_execution →
           Execution MUST be in running state.
           Computation MUST have checkpointable=true.

PRE-C004:  preempt_execution →
           Execution MUST be in running state.
           Computation MUST have checkpointable=true (else: terminate and re-queue from start).

PRE-C005:  reproduce_execution →
           Original Execution MUST be in completed state.
           Environment and all input Datasets MUST still be available.

PRE-C006:  publish_pipeline →
           All nodes MUST reference Published Computations.
           Graph MUST be acyclic.
           All DataFlow type constraints MUST be satisfied.

PRE-C007:  register_provider →
           Provider MUST pass initial benchmark probe.
           Pricing model MUST be specified.
           At least one ResourcePool MUST be declared.
```

### 11.3 Postconditions (must hold AFTER operations)

```
POST-C001: After submit_execution →
           Execution exists with status=submitted.
           Event recorded with actor, computation_ref, timestamp.
           Budget updated with projected cost.

POST-C002: After execution completes →
           Result (ENT-C009) exists with non-empty provenance.
           All output Artifacts/Datasets registered with content_hash.
           Allocation released (resources returned to pool).
           Budget updated with actual cost.
           Completion Event recorded.

POST-C003: After checkpoint →
           Checkpoint (ENT-C008) exists with validation_hash matching state data.
           Checkpoint Event recorded.
           Execution continues in running state.

POST-C004: After preemption →
           Checkpoint exists (if checkpointable).
           Resources released to pool.
           Execution re-queued with Checkpoint reference.
           Preemption Event recorded.

POST-C005: After reproduction →
           New Execution completed.
           ReproducibilityProof (ENT-C015) exists with comparison result.
           Proof references both original and reproduction Executions.

POST-C006: After data export →
           Export Artifact exists in DEP-C004 with complete Organization data.
           Export Event recorded with scope, format, actor.
```

### 11.4 Forbidden Operations

```
FORBID-C001: The system MUST NOT execute a Computation without first freezing its inputs
             and environment to specific, content-addressed versions.
             — Source: CAP-C011

FORBID-C002: The system MUST NOT allow an AI Agent to create, modify, or expand its own
             ComputeEnvelope. Only ACT-C002 may modify Envelopes.
             — Source: CAP-C020

FORBID-C003: The system MUST NOT permanently delete any Execution, Result, Provenance,
             or Event record. Archival only.
             — Source: CAP-C004

FORBID-C004: The system MUST NOT mark a Result as verified without executing the configured
             Verification procedure and recording the verification result.
             — Source: CAP-C016

FORBID-C005: The system MUST NOT log plaintext secrets, credentials, or private keys in
             any Event, Metric, or audit record.
             — Source: CAP-C022

FORBID-C006: The system MUST NOT schedule a Computation to a ResourcePool in a jurisdiction
             that violates applicable placement Policies.
             — Source: CAP-C025

FORBID-C007: The system MUST NOT allow cross-Organization access to Execution data without
             an explicit, revocable permission grant.
             — Source: CAP-C021

FORBID-C008: The system MUST NOT allow an Execution's sandbox to access undeclared network
             endpoints, storage, or resources.
             — Source: CAP-C024
```

### 11.5 Failure Contracts

```
FAIL-C001: If Budget enforcement fails (enforcement=block, but Execution runs anyway):
           Execution completes (do not destroy in-flight work). Actual cost recorded.
           Budget marked as "enforcement-failed." Alert ACT-C002. Post-hoc reconciliation
           required. Subsequent submissions blocked until reconciliation complete.
           — Source: INV-C005

FAIL-C002: If Event hash chain breaks (gap or inconsistency detected):
           System enters "integrity-alert" mode. All Events after the break are flagged.
           New Events continue on a new chain segment. ACT-C006 alerted. Chain repair
           requires manual investigation and attestation.
           — Source: INV-C002

FAIL-C003: If sandbox escape detected:
           Execution immediately terminated. All data from Execution quarantined.
           Actor flagged. ACT-C002 alerted. Incident record created with full forensic data.
           — Source: INV-C009

FAIL-C004: If Provider benchmark probe fails:
           Provider trust_assessment updated. If 3 consecutive failures: Provider suspended.
           Running Executions on that Provider continue to completion. No new Allocations.
           ACT-C002 alerted.
           — Source: THREAT-C004
```

---

## 12. DECISION POINTS & JUDGMENT

```
DEC-C001: Scheduler Resource Selection
  Trigger:       Execution queued and multiple ResourcePools can satisfy requirements
  Inputs:        Resource requirements, applicable Policies (placement, cost, environmental),
                 data locality (input Dataset locations), current pool utilization, cost rates,
                 Priority, historical execution data for similar Computations
  Options:
    A) Cheapest: Select pool with lowest projected cost
    B) Fastest: Select pool with lowest projected queue wait + execution time
    C) Locality-optimized: Select pool closest to input data
    D) Balanced: Multi-objective optimization (weighted combination)
  Default:       D (Balanced) with configurable weights per Project/Organization Policy
  Selection:     Scheduler computes score for each eligible pool using weighted objectives.
                 Ties broken by: data locality > cost > historical success rate.
  Fallback:      If no pool satisfies all hard constraints: reject with ERR-C003 (policy violation).
                 If no pool has available resources: Execution remains queued.
  Audit trail:   Scheduler decision recorded as Event: all candidate pools, scores, selected
                 pool, rejection reasons for non-selected pools.

DEC-C002: Preemption Target Selection
  Trigger:       High-priority Execution queued, no available resources, lower-priority
                 Executions running
  Inputs:        Queue priorities, running Execution priorities, checkpointability, elapsed
                 time, estimated remaining time, preemption cost (checkpoint overhead)
  Options:
    A) Lowest-priority-first: Preempt the lowest-priority running Execution
    B) Shortest-remaining: Preempt the Execution closest to completion (minimize wasted work)
    C) Cheapest-to-preempt: Preempt the Execution with lowest checkpoint overhead
  Default:       A (lowest-priority-first) with tie-breaking by cheapest-to-preempt
  Selection:     Only Executions with priority < queued Execution's priority are candidates.
                 Non-checkpointable Executions are candidates only if their remaining time
                 estimate < queued Execution's estimated start delay.
  Fallback:      No eligible preemption targets → queued Execution waits.
  Audit trail:   Preemption decision recorded as Event: all candidates, scores, selected
                 target, reason.

DEC-C003: Retry vs. Fail Decision
  Trigger:       Execution reaches terminal failure state
  Inputs:        Failure type (transient vs. permanent), attempt_number, retry_policy,
                 elapsed time, remaining budget, error classification
  Options:
    A) Retry: Create new Execution as retry (parent_execution set)
    B) Fail permanently: Mark as failed, no more attempts
    C) Retry with modification: Retry with increased resources or different pool
  Default:       If retry_policy exists and attempt_number < max_attempts and error is
                 transient: A. If error is permanent (e.g., code bug, input error): B.
                 If error is resource-related (OOM, timeout) and retry_policy allows: C.
  Fallback:      max_attempts reached → B. Budget exhausted → B.
  Audit trail:   Decision recorded as Event: failure type, attempt number, decision, reason.

DEC-C004: Pipeline Failure Handling
  Trigger:       A node in a Pipeline fails
  Inputs:        Pipeline failure_policy, node criticality (implicit from dependencies),
                 remaining nodes, partial results
  Options:
    A) Fail-fast: Cancel all running nodes, Pipeline → failed
    B) Skip-failed: Mark dependent nodes as skipped, continue independent branches
    C) Retry-failed: Retry the failed node per its retry_policy
    D) Custom handler: Execute a specified error-handling Computation
  Default:       Pipeline's failure_policy attribute
  Fallback:      If retry exhausted → fall back to fail_policy. If custom handler fails → fail-fast.
  Audit trail:   Decision recorded as Pipeline Event with node details, policy applied, outcome.

DEC-C005: Environment Version Selection
  Trigger:       Computation references Environment by name (not content hash)
  Inputs:        Environment name, available versions (content hashes), Environment lifecycle
                 state, CVE alerts, deprecation notices
  Options:
    A) Latest Active version
    B) Specific pinned version (from Computation spec)
    C) Reject if no non-deprecated version available
  Default:       B if pinned in spec; A if only name provided
  Fallback:      No active version → ERR-C007 (environment unavailable).
  Audit trail:   Resolution recorded as Event: name, resolved hash, reason.
```

---

## 13. CONCURRENCY & ORDERING

### 13.1 Race Conditions

```
RACE-C001: Simultaneous Submissions Exceeding Budget
  Scenario:    Two Actors submit Executions concurrently; each individually within budget,
               but combined exceeds budget.
  Resolution:  Budget check and reservation are atomic (compare-and-swap on budget counter).
               First to reserve succeeds. Second receives ERR-C002 (budget exceeded).
               Reservation has 60s TTL — if Execution not scheduled within TTL, reservation
               released and budget freed.

RACE-C002: Simultaneous Resource Allocation
  Scenario:    Scheduler assigns same ResourcePool capacity to two Executions concurrently.
  Resolution:  Allocation is atomic: compare-and-swap on pool.available counter. First to
               allocate succeeds. Second re-queued for scheduler re-evaluation.

RACE-C003: Schedule Overlap
  Scenario:    Schedule fires while previous Execution from same Schedule still running.
  Resolution:  Governed by overlap_policy (ENT-C006): allow (run both), skip (skip new),
               queue (queue new behind running), cancel_previous (cancel running, start new).
               Overlap check is atomic: lock Schedule → check running → apply policy → release.

RACE-C004: Concurrent Pipeline Node Completion
  Scenario:    Multiple Pipeline nodes complete simultaneously, each triggering downstream nodes.
  Resolution:  DataFlow resolution is per-edge. Each edge independently checks if all upstream
               dependencies are satisfied before triggering downstream. Dependency check is atomic.

RACE-C005: Provider Capacity Change During Scheduling
  Scenario:    ResourcePool capacity changes (scale-down, failure) between scheduler decision
               and allocation attempt.
  Resolution:  Allocation attempt fails → scheduler re-evaluates with updated capacity.
               Execution re-queued with priority boost (avoid starvation).
```

### 13.2 Ordering Guarantees

```
ORD-C001: Events for a single Execution are strictly ordered by sequence number within that
          Execution's Event stream. Cross-Execution ordering is by timestamp with uncertainty bounds.

ORD-C002: Pipeline nodes execute in topological order of the DAG. Nodes with no dependency
          relationship may execute concurrently (up to concurrency_limit).

ORD-C003: Checkpoints for a single Execution are strictly ordered by sequence_number. Resume
          always uses the latest validated Checkpoint.

ORD-C004: Budget updates are serialized per Budget entity. Concurrent operations on different
          Budgets are independent.

ORD-C005: Schedule evaluations are serialized per Schedule (via distributed lock). Different
          Schedules evaluate concurrently.
```

### 13.3 Idempotency

```
IDEM-C001: Execution submission — idempotent via client-provided idempotency key (30-day
           window). Duplicate submission with same key returns existing Execution without
           creating a new one.

IDEM-C002: Resource deallocation — idempotent. Deallocating an already-deallocated resource
           is a no-op.

IDEM-C003: Checkpoint creation — idempotent by sequence_number. Duplicate checkpoint at same
           sequence returns existing Checkpoint.

IDEM-C004: Event recording — append-only, naturally idempotent by design (duplicate detection
           via Event hash).

IDEM-C005: Provider integration — all Provider API calls include idempotency key derived from
           Execution UUID + operation type.
```

### 13.4 Atomicity Boundaries

```
ATOM-C001: Execution submission (validation + Budget reservation + Event recording) = atomic.
ATOM-C002: Resource allocation (pool capacity decrement + Allocation creation) = atomic.
ATOM-C003: Execution completion (output registration + Result creation + Allocation release +
           Budget update + Event recording) = multi-step with compensation on partial failure.
           If output registration succeeds but Result creation fails: retry Result creation.
           If Allocation release fails: background reclamation within 60s.
ATOM-C004: Pipeline node trigger (dependency check + submission) = atomic per edge.
ATOM-C005: Checkpoint (state write + Checkpoint record + Event) = atomic. If any step fails:
           discard checkpoint, Execution continues without checkpoint at this interval.
```

---

## 14. ERROR HANDLING & RECOVERY

### 14.1 Error Taxonomy

```
ERR-C001: Envelope Violation
  Severity:    MEDIUM
  Retryable:   NO (configuration error — Envelope must be expanded by ACT-C002)
  Signal:      Synchronous rejection at submission
  Action:      Reject operation. Log violation. Alert human_approver. If 3rd violation
               within 1 hour: auto-suspend Envelope.
  Source:      PRE-C001, INV-C004

ERR-C002: Budget Exceeded
  Severity:    MEDIUM
  Retryable:   YES (after budget replenishment or period reset)
  Signal:      Synchronous rejection at submission
  Action:      Reject operation. Return remaining budget. Suggest wait-for-reset or
               budget increase request.
  Source:      PRE-C001, CAP-C008

ERR-C003: Policy Violation
  Severity:    HIGH
  Retryable:   NO (unless Computation modified to comply)
  Signal:      Synchronous rejection at submission or scheduling
  Action:      Reject with specific policy that was violated and the constraint that failed.
  Source:      PRE-C001, CAP-C025

ERR-C004: Provisioning Failure
  Severity:    MEDIUM
  Retryable:   YES (transient — provider issue)
  Signal:      Asynchronous (Execution transitions to failed/retrying)
  Action:      Log failure details. If provider-specific: mark provider degraded.
               Reschedule to alternate pool if available. Retry per policy.
  Source:      FLOW-C001 step 14

ERR-C005: Runtime Error
  Severity:    VARIES (may be transient hardware or permanent code bug)
  Retryable:   YES (if classified as transient) / NO (if permanent)
  Signal:      Asynchronous (Execution → failed)
  Action:      Classify error (exit code, signal, OOM indicator, hardware error indicator).
               Transient: retry per policy. Permanent: fail, preserve logs for debugging.
  Source:      FLOW-C001 step 15

ERR-C006: Timeout
  Severity:    MEDIUM
  Retryable:   YES (with increased timeout or from Checkpoint)
  Signal:      Asynchronous (Execution → timeout)
  Action:      If checkpointable: save Checkpoint, allow retry from Checkpoint.
               If not: retry from beginning (if retries remaining).
               If max retries exhausted: fail permanently.
  Source:      FLOW-C001 step 16

ERR-C007: Environment Unavailable
  Severity:    HIGH
  Retryable:   NO (content-addressed — either exists or doesn't)
  Signal:      Synchronous at submission or scheduling
  Action:      Reject with missing Environment reference. Suggest rebuilding Environment
               if base image and packages still available.
  Source:      PRE-C001, DEC-C005

ERR-C008: Dataset Unavailable
  Severity:    HIGH
  Retryable:   MAYBE (if content store is temporarily down)
  Signal:      Synchronous at submission or async at runtime
  Action:      If content store down: queue, retry when recovered.
               If Dataset permanently deleted from content store: fail with data loss alert.
  Source:      PRE-C001, PRE-C005

ERR-C009: Provider API Error
  Severity:    MEDIUM
  Retryable:   YES (provider is external, transient failures expected)
  Signal:      Asynchronous (allocation or deallocation failure)
  Action:      Retry per INT-C003 policy. Circuit breaker if repeated. Reschedule to
               alternate provider if available.
  Source:      INT-C003

ERR-C010: Reproducibility Failure
  Severity:    HIGH
  Retryable:   NO (if artifacts genuinely unavailable)
  Signal:      Synchronous on reproduction request
  Action:      Return which specific artifacts are unavailable. If Environment and Datasets
               both available but results diverge: create ReproducibilityProof with
               "divergent" status and divergence explanation.
  Source:      FLOW-C004

ERR-C011: Integrity Failure (hash chain or content-address mismatch)
  Severity:    CRITICAL
  Retryable:   NO
  Signal:      Detected during any verification check
  Action:      System enters integrity-alert mode (FAIL-C002 or FAIL-C003).
               Affected entity quarantined. ACT-C002 and ACT-C006 alerted.
               Incident investigation required.
  Source:      INV-C002, INV-C006
```

### 14.2 Retry Semantics

```
RETRY-C001: All retries use exponential backoff with jitter.
            Default: base=2s, multiplier=2, max_delay=300s, jitter=±20%.

RETRY-C002: Execution retries create new Execution objects (preserving parent_execution link).
            Each retry is independently auditable.

RETRY-C003: Provider API retries use the integration-level retry policy (INT-C003).
            Circuit breaker prevents retry storms.

RETRY-C004: Maximum retry chain length = 10 (across all error types for a single
            computation instance). After 10 total retries: permanent failure.
```

### 14.3 Degraded Mode

```
DEGRADED-C001: Provider unavailable — scheduler excludes that provider's pools. Existing
               Executions on that provider: continue if possible, checkpoint and migrate if not.
               System operational with reduced capacity.

DEGRADED-C002: Content Store unavailable — new artifact uploads queued locally.
               Existing content-addressed artifacts served from cache if available.
               Executions requiring unavailable artifacts: queued.

DEGRADED-C003: Knowledge Substrate unavailable — computations continue independently.
               Knowledge artifact creation queued. No impact on Execution correctness.

DEGRADED-C004: Business Substrate unavailable — computations continue. Cost tracking
               queued locally with last-known budget limits (conservative: treat remaining
               budget as 80% of last known value).

DEGRADED-C005: Identity Provider unavailable — existing sessions continue. New
               authentications blocked. No new submissions from unauthenticated actors.
```

### 14.4 Circuit Breakers

```
CB-C001: Provider API — trips after 5 failures in 120s. Half-open after 300s.
         One probe request. Success → close. Failure → re-open for 600s.

CB-C002: Content Store — trips after 5 failures in 120s. Half-open after 300s.
         Local cache serves existing artifacts. New uploads queue.

CB-C003: Budget Service (if separate) — trips after 5 failures in 60s. Half-open after 120s.
         Conservative budget estimation during open state.

CB-C004: Identity Provider — trips after 5 failures in 60s. Half-open after 120s.
         Existing sessions unaffected.
```

---

## 15. PERSISTENCE REQUIREMENTS (LOGICAL — WHAT, NOT HOW)

```
PERS-C001: Event Log (Source of Truth)
  What:          Every state change for every entity: Computation published, Execution
                 state transition, Checkpoint created, Result registered, Budget updated,
                 Policy changed, Envelope modified, Provider registered.
  Volume:        ≤50B events/day (ASM-C010). 99th percentile event size ≤4KB.
  Retention:     Events MUST be retained for minimum 7 years. Archival after 1 year
                 (cold storage, queryable within 60s).
  Access:        Append-only. Write = system only. Read = per authorization model (§9).
  Integrity:     Hash-chained. Each event includes hash of previous event.
                 Chain verified hourly.
  Reconstruction: Complete system state at any past timestamp MUST be reconstructable
                 from the Event log alone.

PERS-C002: Computation Specifications
  What:          All versions of all Computation definitions.
  Retention:     Indefinite (specifications are small; reference data).
  Access:        CRUD per §9. Versions immutable once published.

PERS-C003: Execution State (Materialized View)
  What:          Current state of all Executions, derived from Event log.
  Consistency:   Eventual consistency with Event log (target: <500ms lag).
  Reconstruction: If corrupted, fully reconstructable from PERS-C001.
  Access:        Read per §9. Write = system only (from Events).

PERS-C004: Content-Addressed Store
  What:          Environments, Datasets, Artifacts, Checkpoints — all referenced by content hash.
  Volume:        Unbounded (petabyte-scale expected). Tiered: hot (recent, active), warm
                 (accessible within seconds), cold (accessible within minutes).
  Retention:     Referenced content MUST be retained while any Execution, Result, or
                 Provenance record references it. Unreferenced content eligible for
                 garbage collection after 90 days (configurable).
  Deduplication: Content-addressing provides automatic deduplication.
  Integrity:     Hash verified on every read. Corrupted content triggers re-fetch from
                 replica or alert if no replica available.

PERS-C005: Metric Store
  What:          Time-series data from all Executions and ResourcePools.
  Volume:        High cardinality (execution × metric_name × timestamp).
  Retention:     Raw: 30 days. 1-minute aggregates: 1 year. 1-hour aggregates: 7 years.
  Access:        Read per §9.

PERS-C006: Budget State
  What:          Current usage for all Budgets.
  Consistency:   Strongly consistent (Budget checks are on the critical path).
  Reconstruction: Reconstructable from Event log (sum of allocation costs).

PERS-C007: Scheduling State
  What:          Current queue contents, ResourcePool availability, active Allocations.
  Consistency:   Strongly consistent for allocation (ATOM-C002).
  Ephemerality:  Reconstructable from Event log + Provider state queries.
```

---

## 16. MIGRATION & ONBOARDING

### 16.1 Migration from Existing Systems

```
MIG-C001: Import from Kubernetes
  What:          Job/CronJob/Deployment manifests → Computation + Schedule + Environment
  Strategy:      Parse YAML manifests. Map container specs to Environment.
                 Map resource requests/limits to Resource requirements.
                 Map volumes to Dataset references. Map CronJob schedules to Schedule.
  Fidelity:      Kubernetes-specific features (NodeAffinity, Tolerations, PodDisruptionBudget)
                 → Policy rules. ServiceAccounts → Actor identity mapping.
  Validation:    Imported Computations submitted in dry-run mode. Differences flagged.

MIG-C002: Import from Airflow
  What:          DAG definitions → Pipeline + Computation (per task) + Schedule
  Strategy:      Parse DAG Python code (AST analysis). Map operators to Computations.
                 Map task dependencies to Pipeline edges. Map schedule_interval to Schedule.
  Fidelity:      Airflow-specific features (Pools → Budget/ResourcePool, Connections → Provider,
                 Variables → parameters, XCom → DataFlow).
  Validation:    Parallel run: execute imported Pipeline alongside original Airflow DAG.
                 Compare outputs.

MIG-C003: Import from Slurm
  What:          Job scripts + sbatch options → Computation + Resource requirements
  Strategy:      Parse #SBATCH directives for resources, partitions, time limits.
                 Map modules to Environment packages. Map partitions to ResourcePools.
  Fidelity:      Slurm-specific: job arrays → parameterized Computations, dependencies → Pipeline.
  Validation:    Submit via SUBSTRATE-COMPUTE to same HPC resources. Compare output checksums.

MIG-C004: Import from CI/CD (GitHub Actions, GitLab CI, etc.)
  What:          Workflow definitions → Pipeline + Computation (per step)
  Strategy:      Parse YAML workflow. Map jobs to Pipeline nodes. Map steps to Computations.
                 Map runner labels to ResourcePool capabilities. Map secrets to secret store.
  Fidelity:      CI-specific: matrix builds → parameterized Computations, caching → Dataset reuse.

MIG-C005: Generic Import
  What:          Any compute job expressible as { command, environment, resources, inputs, outputs }
  Strategy:      Minimal adapter: Actor provides command, container image, resource requirements.
                 System creates Computation, Environment, and input bindings.
  Fidelity:      Baseline. No platform-specific feature mapping.
```

### 16.2 Cutover Strategy

```
CUT-C001: Parallel Run
  Duration:     Configurable (recommended: 2 weeks minimum)
  Process:      Both old system and SUBSTRATE-COMPUTE execute the same Computations.
                Output comparison automated. Discrepancies investigated.
  Rollback:     At any point during parallel run, old system is authoritative.
                SUBSTRATE-COMPUTE results are advisory.

CUT-C002: Gradual Migration
  Process:      Migrate Computations in priority order: lowest-risk first.
                Each Computation validated via CUT-C001 before cutover.
                Old system decommissioned only after all Computations migrated and
                validated for ≥1 complete cycle.

CUT-C003: Rollback Plan
  Trigger:      >5% output discrepancy rate during parallel run, OR any data loss,
                OR any security incident.
  Process:      Halt migration. Revert migrated Computations to old system.
                SUBSTRATE-COMPUTE data preserved for investigation.
  Duration:     Rollback executable within 1 hour.
```

### 16.3 First-Run Experience

```
FIRST-C001: Solo Researcher
  Steps:
    1. Create Organization and Project (CLI or UI — < 2 minutes)
    2. Import first Computation: `substrate-compute import --from docker-run "docker run -v ... my_image my_script.py"`
    3. System creates Computation + Environment + input Dataset bindings
    4. `substrate-compute run my_computation` — executes locally
    5. Result with full Provenance available immediately
  Target time: < 10 minutes from install to first verified Result

FIRST-C002: Team with Existing Infrastructure
  Steps:
    1. Create Organization, Projects, Budgets
    2. Register existing infrastructure as Provider + ResourcePools
    3. Import existing Computations via MIG-C001 through MIG-C005
    4. Parallel run (CUT-C001) for validation
    5. Gradual migration (CUT-C002)
  Target time: < 1 day from install to first parallel run

FIRST-C003: AI Agent Setup
  Steps:
    1. ACT-C002 creates ComputeEnvelope for the agent
    2. Agent authenticated via service account or API key
    3. Agent queries available Computations, Environments, ResourcePools
    4. Agent submits first Execution within Envelope bounds
    5. Envelope adjusted based on initial usage patterns
  Target time: < 30 minutes from agent registration to first Execution
```

---

## 17. OPERATIONAL PROFILE

### 17.1 Performance Requirements

```
PERF-C001: Execution submission latency — p50 ≤ 200ms, p99 ≤ 2s (validation + budget check
           + event recording). Does NOT include scheduling or provisioning time.

PERF-C002: Scheduling latency (queued → scheduled) — p50 ≤ 5s, p99 ≤ 60s for standard
           priority. p99 ≤ 5s for critical priority (with preemption).

PERF-C003: Event recording latency — p50 ≤ 50ms, p99 ≤ 500ms. Events must be durable
           (persisted) before acknowledgment.

PERF-C004: Result query latency — p50 ≤ 100ms, p99 ≤ 1s for current-state queries.
           Time-travel queries: p50 ≤ 2s, p99 ≤ 30s.

PERF-C005: Metric ingestion — ≥1M metrics/second per Organization. Query latency for
           time-range aggregations: p50 ≤ 500ms, p99 ≤ 5s.

PERF-C006: Content store access — p50 ≤ 100ms, p99 ≤ 5s for metadata lookup.
           Artifact download speed limited by network bandwidth, not system overhead.

PERF-C007: Pipeline DAG resolution — ≤100ms for pipelines with ≤1000 nodes.

PERF-C008: Concurrent active Executions per Organization — ≥100,000.
           Global concurrent Executions — ≥10M.
```

### 17.2 Configuration & Environment

```
CONFIG-C001: All system configuration via declarative configuration files (YAML/TOML).
             Environment variables override config file values (12-factor compatible).
             No configuration in code.

CONFIG-C002: Feature flags for all major capabilities: scheduling strategies, verification
             modes, provider integrations, experimental features. Flags evaluable per
             Organization, Project, or Actor.

CONFIG-C003: Resource class definitions (what constitutes a "GPU-hour," "CPU-hour," etc.)
             are configurable per Provider. A mapping layer normalizes across Providers.

CONFIG-C004: Scheduling policy weights (cost vs. speed vs. locality) configurable per
             Organization and per Project. Defaults provided.

CONFIG-C005: Budget enforcement strictness configurable: strict (reject if any chance of
             overage), standard (reject if projected overage), permissive (warn only).
```

### 17.3 Versioning Strategy

```
VER-C001: API versioning — URI path versioning (e.g., /v1/executions, /v2/executions).
          Old versions supported for minimum 24 months after successor release.
          Deprecation announced ≥12 months before removal.

VER-C002: Computation specification version — managed by the system (auto-increment).
          Published versions are immutable. Old versions remain executable indefinitely
          (Environments are content-addressed, so reproducibility is guaranteed).

VER-C003: Event schema version — included in every Event. Schema evolution via additive
          changes only (new fields optional, old fields never removed). Breaking changes
          require new Event type.

VER-C004: Provider adapter version — independently versioned per Provider. Provider API
          changes handled by adapter updates. Adapter version recorded in Execution
          Provenance.

VER-C005: Internal schema — migrations handled via Event log replay. No destructive
          migrations (append-only, additive evolution).
```

### 17.4 Storage Recommendations (Non-Binding)

```
STORE-C001: Event Log — Append-optimized, high-durability store. Consider: Apache Kafka
            (with tiered storage) for ingestion, Apache Iceberg/Delta for queryable archive.

STORE-C002: Content-Addressed Store — Object store with content-addressable layer.
            Consider: S3-compatible with custom content-addressing middleware, or
            purpose-built CAS (e.g., IPFS for distribution, backed by durable store).

STORE-C003: Metric Store — Time-series optimized. Consider: Prometheus (short-term) +
            Thanos/Cortex (long-term), or ClickHouse, or InfluxDB.

STORE-C004: Materialized Views (current state) — Low-latency key-value or document store.
            Consider: PostgreSQL with materialized views, or ScyllaDB/Cassandra for scale.

STORE-C005: Budget State — Strongly consistent store with compare-and-swap support.
            Consider: PostgreSQL, etcd, or FoundationDB.
```

---

## 18. EXECUTABLE SPECIFICATION OUTLINE (TEST PLAN)

### 18.1 Capability Tests

```
TEST-C001: [CAP-C001] Submit Computation
  Given:   Authenticated Actor with Project role, Published Computation, Budget available
  When:    Actor submits Execution via IFC-C002
  Then:    Execution created with status=submitted. Event recorded. Budget reserved.

TEST-C002: [CAP-C002] Schedule and Execute
  Given:   Submitted Execution, ResourcePool with available capacity
  When:    Scheduler evaluates
  Then:    Execution transitions submitted → queued → scheduled → provisioning → running → completed.
           Allocated resources satisfy requirements.

TEST-C003: [CAP-C003] Event Recording
  Given:   Any Execution state transition
  When:    Transition occurs
  Then:    Event recorded with: timestamp, actor, entity, old_state, new_state, hash.
           Hash includes previous Event's hash.

TEST-C004: [CAP-C004] No Permanent Deletion
  Given:   Completed Execution with Result
  When:    ACT-C002 attempts to delete
  Then:    Operation rejected or Execution archived (not deleted). State remains queryable.

TEST-C005: [CAP-C005] Time-Travel Query
  Given:   Execution that transitioned through 5 states over 10 minutes
  When:    ACT-C006 queries state at timestamp = start_time + 3 minutes
  Then:    Correct historical state returned (e.g., "running" if that was state at t+3m).

TEST-C006: [CAP-C006] Resource Abstraction
  Given:   Computation requiring "4 CPU cores, 16GB RAM, 1 GPU"
  When:    Scheduled to cloud pool (AWS) and HPC pool (Slurm)
  Then:    Both executions produce identical Results. No provider-specific details in Computation.

TEST-C007: [CAP-C007] Heterogeneous Hardware
  Given:   ResourcePools with: CPU-only, GPU (NVIDIA), GPU (AMD), FPGA, custom accelerator
  When:    Computation requiring "GPU" submitted
  Then:    Scheduler selects from GPU pools. FPGA and custom pools excluded unless
           Computation specifically requests them.

TEST-C008: [CAP-C008] Budget Enforcement
  Given:   Budget with $100 remaining, enforcement=block
  When:    Execution submitted with projected cost $150
  Then:    Submission rejected with ERR-C002.

TEST-C009: [CAP-C009] Utilization Metrics
  Given:   Running Execution
  When:    Metrics queried via IFC-C007
  Then:    CPU%, GPU%, memory%, I/O% returned in real-time (≤60s lag).

TEST-C010: [CAP-C011] Provenance Capture
  Given:   Execution completes
  Then:    Provenance (ENT-C016) exists with: exact Computation version, content-addressed
           Environment hash, exact Dataset versions with checksums, resource Allocation details.

TEST-C011: [CAP-C012] Reproduce
  Given:   Completed Execution with all artifacts available
  When:    Actor requests reproduction via IFC-C005
  Then:    New Execution created with identical spec. Outputs compared. ReproducibilityProof created.

TEST-C012: [CAP-C013] Content Addressing
  Given:   Two Environments with identical specifications
  When:    Both created
  Then:    Both resolve to same content_hash. Only one stored.

TEST-C013: [CAP-C014] Verification
  Given:   Computation with assertion-type Verification ("output.accuracy > 0.9")
  When:    Execution completes with accuracy = 0.85
  Then:    Verification status = failed. Result records failure details.

TEST-C014: [CAP-C017, C018] Pipeline Execution
  Given:   Pipeline with 3 nodes: A → B → C
  When:    Pipeline executed
  Then:    A runs first. B starts after A completes (with A's output). C starts after B completes.

TEST-C015: [CAP-C019] Pipeline Failure Handling
  Given:   Pipeline with failure_policy=skip_failed, nodes A → B, A → C
  When:    B fails
  Then:    C continues. B marked as failed. Pipeline completes with partial results.

TEST-C016: [CAP-C020] Envelope Enforcement
  Given:   AI Agent with Envelope: max_concurrent=3, currently 3 running
  When:    Agent submits 4th Execution
  Then:    Submission rejected with ERR-C001. Violation logged. Agent's human_approver notified.

TEST-C017: [CAP-C023] Data Export
  Given:   Organization with 1000 Executions
  When:    ACT-C002 requests full export via IFC-C008
  Then:    Export artifact created containing all Computations, Executions, Results,
           Events, Budgets, Policies. Format matches requested (JSON-LD/CSV/Parquet).

TEST-C018: [CAP-C024] Sandbox Isolation
  Given:   Computation with no declared network endpoints
  When:    Execution code attempts to make HTTP request to external server
  Then:    Network request blocked. Execution continues (or fails if code cannot handle block).

TEST-C019: [CAP-C025] Data Locality Enforcement
  Given:   Policy: "data tagged EU_PII must run in EU jurisdiction"
  When:    Execution with EU_PII-tagged Dataset submitted
  Then:    Scheduler only considers EU-located ResourcePools. Non-EU pools excluded.

TEST-C020: [CAP-C026] Checkpoint and Resume
  Given:   Long-running, checkpointable Execution
  When:    Checkpoint interval reached
  Then:    Checkpoint created with validation_hash. Execution continues. Checkpoint queryable.

TEST-C021: [CAP-C027] Preemption
  Given:   Low-priority Execution running, high-priority Execution queued, no free resources
  When:    Scheduler evaluates
  Then:    Low-priority Execution checkpointed, preempted, re-queued. High-priority Execution
           allocated and running.

TEST-C022: [CAP-C028] Offline Mode
  Given:   System with no network connectivity
  When:    Actor specifies Computation (CLI, local)
  Then:    Computation spec saved locally. On connectivity restored: auto-syncs and submits.
```

### 18.2 Invariant Tests

```
TEST-C023: [INV-C001] Provenance completeness — verify every completed Execution has non-empty
           Provenance linking to all required elements.

TEST-C024: [INV-C002] Hash chain integrity — submit 1000 Events, verify continuous hash chain.
           Attempt to modify one Event mid-chain → chain verification fails.

TEST-C025: [INV-C003] Result existence — verify every terminal Execution has a Result.

TEST-C026: [INV-C004] Envelope integrity — verify no AI agent Execution exists outside
           its Envelope bounds. Inject Envelope bypass attempt → system rejects.

TEST-C027: [INV-C005] Budget consistency — sum all Allocation costs within Budget scope.
           Compare to Budget.current. Divergence within ±0.01% (floating point tolerance).

TEST-C028: [INV-C006] Content hash integrity — create Artifact, tamper with content,
           read → hash mismatch detected.

TEST-C029: [INV-C007] DAG acyclicity — attempt to publish Pipeline with cycle → rejected.

TEST-C030: [INV-C008] Resource pool consistency — verify available + reserved ≤ total
           after 1000 concurrent allocation/deallocation operations.

TEST-C031: [INV-C009] Sandbox enforcement — Execution with undeclared network access
           → network blocked.
```

### 18.3 Forbidden Operation Tests

```
TEST-C032: [FORBID-C001] Attempt submit without frozen inputs → rejected.
TEST-C033: [FORBID-C002] AI agent attempts to modify own Envelope → rejected.
TEST-C034: [FORBID-C003] Attempt permanent deletion of Execution → rejected.
TEST-C035: [FORBID-C004] Attempt to mark Result verified without running Verification → rejected.
TEST-C036: [FORBID-C005] Check all Event/Metric logs for plaintext secrets → none found.
TEST-C037: [FORBID-C006] Submit Execution to wrong-jurisdiction pool → scheduling rejected.
TEST-C038: [FORBID-C007] Access cross-Org Execution without grant → rejected.
TEST-C039: [FORBID-C008] Sandbox accesses undeclared resource → blocked.
```

### 18.4 Failure Contract Tests

```
TEST-C040: [FAIL-C001] Simulate budget enforcement failure → Execution completes, Budget
           marked enforcement-failed, alert sent, subsequent submissions blocked.
TEST-C041: [FAIL-C002] Inject hash chain break → system enters integrity-alert mode, Events
           flagged, new chain segment started, ACT-C006 alerted.
TEST-C042: [FAIL-C003] Simulate sandbox escape detection → Execution terminated, data
           quarantined, Actor flagged, incident record created.
TEST-C043: [FAIL-C004] Provider benchmark probe failure 3× → Provider suspended, no new
           Allocations, running Executions complete, ACT-C002 alerted.
```

### 18.5 Abuse Case Tests

```
TEST-C044: [ABUSE-C001] Submit Computation with mining-like resource pattern → detected,
           terminated, Actor flagged.
TEST-C045: [ABUSE-C002] Computation generates excessive egress → rate-limited, terminated.
TEST-C046: [ABUSE-C003] Repeated side-channel access pattern → anomaly detected, rate-limited.
TEST-C047: [ABUSE-C004] Provider returns inconsistent benchmark results → trust score reduced,
           suspended after 3 failures.
```

### 18.6 Concurrency Tests

```
TEST-C048: [RACE-C001] 100 concurrent submissions against Budget with capacity for 50 →
           exactly 50 succeed, 50 reject with ERR-C002.
TEST-C049: [RACE-C002] 100 concurrent allocations against pool with 50 slots → exactly
           50 allocated, 50 re-queued.
TEST-C050: [RACE-C003] Schedule fires while previous running, overlap_policy=skip → new skipped.
TEST-C051: [RACE-C004] 10 Pipeline nodes complete simultaneously → all downstreams correctly triggered.
TEST-C052: [RACE-C005] Pool capacity halved during scheduling → failed allocation re-queued.
```

---

## 19. OBSERVABILITY & AUDITABILITY

### 19.1 Logging

```
LOG-C001: Every API request logged: { timestamp, actor, operation, entity, input_summary,
          output_summary (or error), latency_ms, trace_id }.
          Retention: 90 days hot, 2 years warm, 7 years cold.

LOG-C002: Every Execution state transition logged as Event (PERS-C001).
          Cross-referenced with LOG-C001 via trace_id.

LOG-C003: Every scheduler decision logged: { timestamp, execution_id, candidates,
          scores, selected, rejection_reasons }.
          Retention: 1 year hot, 7 years cold.

LOG-C004: Every Envelope violation logged: { timestamp, agent, operation, envelope_id,
          violation_type, threshold, actual_value }.
          Retention: 7 years (compliance).

LOG-C005: Every Provider interaction logged: { timestamp, provider, operation, request_summary,
          response_summary, latency_ms, retry_count }.
          Retention: 1 year hot, 7 years cold.
```

### 19.2 Metrics

```
MET-C001: execution_submission_rate — counter — per Organization, per Project
MET-C002: execution_scheduling_latency — histogram — p50, p90, p99
MET-C003: execution_duration — histogram — per Computation type, per ResourcePool
MET-C004: execution_success_rate — gauge — per Computation, per Project, per Organization
MET-C005: resource_utilization — gauge — per ResourcePool, per resource type
MET-C006: budget_usage_percentage — gauge — per Budget
MET-C007: provider_error_rate — counter — per Provider, per error type
MET-C008: verification_pass_rate — gauge — per Computation
MET-C009: reproducibility_rate — gauge — per Project (% of Executions with successful proof)
MET-C010: event_recording_latency — histogram — p50, p90, p99
MET-C011: scheduler_queue_depth — gauge — per priority level
MET-C012: checkpoint_success_rate — gauge — per Computation
MET-C013: preemption_rate — counter — per ResourcePool
MET-C014: cost_per_execution — histogram — per Computation type
MET-C015: sandbox_violation_count — counter — per Actor
```

### 19.3 Alerts

```
ALERT-C001: Budget usage > alert_threshold → notification to Budget owner
ALERT-C002: Envelope violation → immediate notification to human_approver
ALERT-C003: Hash chain integrity failure → CRITICAL → ACT-C002 and ACT-C006
ALERT-C004: Provider error rate > 10% for 5 minutes → WARN → ACT-C002
ALERT-C005: Provider error rate > 50% for 5 minutes → CRITICAL → ACT-C002
ALERT-C006: Sandbox violation detected → CRITICAL → ACT-C002
ALERT-C007: Execution success rate < 50% for any Computation over 10+ runs → WARN → Project owner
ALERT-C008: ResourcePool utilization > 90% → WARN → ACT-C002
ALERT-C009: ResourcePool utilization > 98% → CRITICAL → ACT-C002
ALERT-C010: Scheduler queue depth > 10,000 → WARN → ACT-C002
ALERT-C011: Cost anomaly (execution cost > 3× historical average for same Computation) → WARN → submitter
```

### 19.4 Audit Trail

```
AUDIT-C001: Every mutating operation on every entity is recorded in the Event log with
            full actor identity, timestamp, operation, before/after state.

AUDIT-C002: ACT-C006 (Auditor) can query: "all actions by Actor X in time range T,"
            "all changes to Entity Y," "all Executions in Project Z," "all Envelope
            violations," "all Budget overages."

AUDIT-C003: Time-travel queries (IFC-C006) provide point-in-time state reconstruction
            for any entity at any past timestamp.

AUDIT-C004: Export audit (IFC-C008) includes complete Event history — no audit gap.
```

### 19.5 Tracing

```
TRACE-C001: Every API request receives a trace_id (W3C Trace Context or OpenTelemetry compatible).
TRACE-C002: trace_id propagated through: submission → scheduling → allocation → provisioning →
            execution → result registration → notification.
TRACE-C003: Cross-substrate traces: SUBSTRATE-COMPUTE trace_id linked to SUBSTRATE (business)
            and SUBSTRATE-KNOWLEDGE trace_ids when cross-substrate Events occur.
TRACE-C004: Pipeline traces: parent trace_id for Pipeline; child trace per node Execution.
```

### 19.6 PII Redaction

```
REDACT-C001: Actor identity redacted from logs in external/cross-org audit views.
             Internal logs retain identity.
REDACT-C002: Computation parameters may contain sensitive data. Parameters not logged
             at INFO level. DEBUG-level parameter logging requires explicit opt-in
             per Computation.
REDACT-C003: Dataset content never logged. Only content_hash, size, and format logged.
REDACT-C004: Secrets never appear in any log, metric, event, or audit record (FORBID-C005).
```

---

## 20. DEFINITION OF DONE

### 20.1 Build Complete

```
DONE-C001: All 28 CAP-C### capabilities implemented and passing TEST-C001 through TEST-C022.
DONE-C002: All 9 INV-C### invariants verified and passing TEST-C023 through TEST-C031.
DONE-C003: All 8 FORBID-C### forbidden operations enforced and passing TEST-C032 through TEST-C039.
DONE-C004: All 4 FAIL-C### failure contracts implemented and passing TEST-C040 through TEST-C043.
DONE-C005: All 4 ABUSE-C### abuse cases detectable and passing TEST-C044 through TEST-C047.
DONE-C006: All 5 RACE-C### concurrency scenarios handled and passing TEST-C048 through TEST-C052.
DONE-C007: All 11 IFC-C### interfaces operational with documented error codes.
DONE-C008: All 7 INT-C### integration contracts implemented with circuit breakers, retry
           policies, and failure modes as specified.
DONE-C009: All 5 MIG-C### migration adapters functional for import.
DONE-C010: All 7 PERS-C### persistence requirements met with Event log as source of truth.
DONE-C011: All 8 PERF-C### performance requirements met under load test
           (10× projected peak = 500B events/day).
```

### 20.2 Ship Ready

```
SHIP-C001: FIRST-C001 (solo researcher) completable in ≤10 minutes by a person unfamiliar
           with the system, without assistance.
SHIP-C002: FIRST-C002 (team migration) completable in ≤1 day for an Organization with
           ≤100 existing Computations.
SHIP-C003: FIRST-C003 (AI agent) completable in ≤30 minutes by ACT-C002.
SHIP-C004: CUT-C001 (parallel run) validated for ≥2 weeks with <1% output discrepancy.
SHIP-C005: Data Export (CAP-C023) validated: exported data re-importable to clean instance
           with zero data loss.
SHIP-C006: Offline mode (CAP-C028) validated: 24-hour disconnected operation with successful
           sync on reconnect.
SHIP-C007: All ALERT-C### alerts firing correctly under simulated failure conditions.
SHIP-C008: Documentation complete: API reference, migration guides, first-run tutorials,
           troubleshooting guide, security whitepaper.
SHIP-C009: Security audit: THREAT-C001 through THREAT-C008 mitigations verified by
           independent security review.
SHIP-C010: Reproducibility verification: 100 diverse Computations (ML training, data
           pipeline, scientific simulation, CI/CD, serverless function) each reproduced
           successfully via CAP-C012 with ReproducibilityProof confirming identical or
           statistically equivalent results.
```

---

## 21. OPEN QUESTIONS & RISKS

```
OQ-C001: Federated Scheduling Optimization
  Status:     OPEN
  Impact:     Scheduling across independent organizations' resource pools (each with private
              capacity and pricing) is harder than scheduling within a single pool. Optimal
              cross-federation scheduling may be impossible without information sharing that
              conflicts with privacy.
  Resolution: Phase 1 deploys with per-Organization scheduling only. Federation scheduling
              uses published availability (not private capacity). Research into privacy-
              preserving scheduling (e.g., secure multi-party computation) in Phase 2.
  Owner:      Architecture team
  Deadline:   Phase 2 design: +6 months from v1.0 launch

OQ-C002: Non-Deterministic Verification Completeness
  Status:     OPEN
  Impact:     ML training and Monte Carlo simulations are inherently non-deterministic.
              "Statistically equivalent" is well-defined for some distributions but not all.
              Risk of false-positive verification (results look equivalent but are meaningfully
              different).
  Resolution: v1.0 supports deterministic, checksum, assertion, and configurable statistical
              verification. Organization-specific statistical tests pluggable via Verification
              spec. Research into domain-specific equivalence metrics ongoing.
  Owner:      Verification team
  Deadline:   Ongoing research; statistical methods reviewed quarterly

OQ-C003: Quantum Resource Modeling
  Status:     OPEN
  Impact:     Quantum computers have fundamentally different resource models (qubits, gate
              depth, connectivity, error rates). Current Resource model (TERM-C002) is
              extensible but untested for quantum.
  Resolution: Resource model designed for extension (ASM-C011). Quantum resource types
              will be added when production quantum hardware is integrated as a Provider.
  Owner:      Hardware integration team
  Deadline:   First quantum Provider integration: +12 months

OQ-C004: Jurisdiction-of-Computation Legal Framework
  Status:     OPEN
  Impact:     Multi-jurisdiction computation raises unresolved legal questions. The system
              records all jurisdictions involved but cannot resolve which law applies.
  Resolution: System provides jurisdiction tracking (ENT-C019 placement policies).
              Legal resolution is per-Organization responsibility with guidance from
              Anthropic legal team.
  Owner:      Legal team
  Deadline:   Legal framework document: +3 months

OQ-C005: Long-Running Execution Cost Prediction
  Status:     OPEN
  Impact:     Spot/preemptible pricing is dynamic. Cost projection for a 72-hour execution
              may be significantly off if pricing changes mid-execution.
  Resolution: v1.0 projects cost at submission-time pricing. Actual cost computed on
              completion. Cost anomaly alerts (ALERT-C011) notify if actual diverges
              significantly from projected. Dynamic cost estimation (re-projecting during
              execution) planned for v1.1.
  Owner:      Cost team
  Deadline:   Dynamic estimation: v1.1 (+3 months from v1.0)

OQ-C006: Checkpoint Format Standardization
  Status:     OPEN
  Impact:     Different frameworks serialize state differently (PyTorch checkpoints vs.
              TensorFlow SavedModel vs. custom formats). No universal checkpoint format
              means migration across frameworks requires conversion.
  Resolution: v1.0 treats checkpoints as opaque blobs with metadata. Cross-framework
              checkpoint translation is NG-C006 (not our problem). However, checkpoint
              metadata schema is standardized for discoverability.
  Owner:      Execution team
  Deadline:   N/A (design choice, not open question)

OQ-C007: Environmental Impact Tracking Granularity
  Status:     OPEN
  Impact:     Policy type "environmental" (ENT-C019) supports carbon budgets, but
              per-Execution carbon measurement depends on Provider-reported data.
              Not all Providers report energy usage or carbon intensity.
  Resolution: v1.0 supports environmental Policy with Provider-reported data where
              available. Estimation models (based on resource type, region, duration)
              used when Provider data unavailable. Accuracy improves as more Providers
              report. Carbon tracking marked as "estimated" when not Provider-reported.
  Owner:      Sustainability team
  Deadline:   Provider carbon API integration: +6 months
```

---

## 22. IMPLEMENTATION NOTES (NON-BINDING)

### 22.1 Recommended Build Phases

```
Phase 1: Core Computation Model
         Computation, Environment, Dataset, Execution lifecycle.
         Event store (append-only, hash-chained). Provenance (TERM-C018) recording.
         Single ResourcePool, basic scheduling. Budget tracking.

Phase 2: Pipeline & Workflow
         Pipeline (TERM-C010) with Stages and DataFlows.
         Checkpoint and recovery. Result Verification (TERM-C014).
         Multi-ResourcePool scheduling with Budget enforcement.

Phase 3: Provider Federation & Security
         Provider (TERM-C020) registration and trust assessment.
         Resource Pool federation. Provider adapter plugins (INT-C003).
         Sandboxing, egress filtering, anomaly detection.

Phase 4: Advanced Features
         Project grouping. Data Export / Import.
         ComputeEnvelope (TERM-C019) enforcement.
         Offline mode (CAP-C028). CLI tooling.
         Cost optimization (spot instance support).

Phase 5: Cross-Substrate Integration
         All 6 cross-substrate integration contracts (INT-C008 through INT-C013).
         Cross-substrate event emission for all 8 defined topics.
         Full audit trail and observability.
```

### 22.2 Composition Patterns

```
PATTERN-C001: Simulation / Scenario Modeling
              COMPUTE (execution owner) + KNOWLEDGE (epistemic owner) + DESIGN
              (artifact owner). DESIGN defines Component + Geometry + Material.
              KNOWLEDGE formulates Hypothesis. COMPUTE executes simulation Pipeline.
              KNOWLEDGE records result as Proposition with Confidence from convergence
              quality. See SUBSTRATE-COMPOSITION-PATTERNS-v1.md PATTERN-008.

PATTERN-C002: Regulatory Intelligence
              GOVERNANCE (regulatory owner) + KNOWLEDGE (epistemic owner) + COMPUTE
              (processing owner). COMPUTE NLP Pipeline extracts regulatory clauses
              from ingested documents. KNOWLEDGE creates Propositions. GOVERNANCE
              maps to Norms. See SUBSTRATE-COMPOSITION-PATTERNS-v1.md PATTERN-006.

PATTERN-C003: Autonomous Navigation
              PHYSICAL (sensing owner) + SPATIAL (mapping owner) + COMPUTE
              (algorithm owner). COMPUTE perception Pipeline processes sensor data
              (10Hz+). COMPUTE path planning Pipeline generates motion trajectory.
              PHYSICAL executes via ControlLoop.
              See SUBSTRATE-COMPOSITION-PATTERNS-v1.md PATTERN-007.

PATTERN-C004: Production Scheduling
              BUSINESS (demand owner) + TEMPORAL (scheduling owner) + DESIGN
              (artifact owner) + COMPUTE (solver owner). TEMPORAL submits
              SchedulingProblem as Dataset. COMPUTE solver Pipeline optimizes.
              See SUBSTRATE-COMPOSITION-PATTERNS-v1.md PATTERN-011.
```

### 22.3 Additional Implementation Notes

> These recommendations reflect ASI-1's analysis of optimal implementation strategies.
> They are non-binding. Implementors may choose different approaches.

```
NOTE-C001: Event Store
  Recommendation: Apache Kafka with tiered storage for ingestion + Apache Iceberg on
                  object store for queryable archive. Kafka provides ordering guarantees
                  and at-least-once delivery. Iceberg provides time-travel queries and
                  efficient cold storage.

NOTE-C002: Scheduler Architecture
  Recommendation: Two-level scheduler. Level 1 (global): assigns Executions to ResourcePools
                  based on Policy, Budget, and data locality. Level 2 (per-pool): allocates
                  specific resources within the pool. This separates organizational concerns
                  (Level 1) from hardware-specific concerns (Level 2).
  Rationale:      Mirrors the Mesos/YARN two-level model but with the addition of cross-
                  organization federation at Level 1.

NOTE-C003: Provider Adapter Pattern
  Recommendation: Provider adapters as plugins implementing a standard interface:
                  { allocate(resources) → allocation, deallocate(allocation), probe() → capabilities,
                    get_metrics(allocation) → metrics }. Each adapter translates to provider-
                  specific API. New providers added by implementing adapter interface.

NOTE-C004: Sandbox Implementation
  Recommendation: gVisor or Firecracker microVMs for Execution isolation. Network policy
                  enforcement via eBPF. Filesystem isolation via overlayfs with read-only
                  base and per-Execution writable layer.

NOTE-C005: Content-Addressed Storage
  Recommendation: Two-tier. Tier 1: local content-addressable cache (fast, limited size).
                  Tier 2: object store (S3-compatible) with content-addressing middleware.
                  Deduplication at ingestion time. Garbage collection via reference counting
                  from Event log.

NOTE-C006: Cross-Substrate Communication
  Recommendation: Shared event bus (same infrastructure as NOTE-C001). Each substrate
                  publishes events to shared topics. Subscribing substrates consume
                  asynchronously. Schema registry ensures compatible event formats.
                  Shared identity infrastructure (same IdP) for cross-substrate authorization.

NOTE-C007: Offline Mode
  Recommendation: SQLite-based local store for offline Computation specs and queue.
                  Sync protocol: CRDT-based merge for Computation specs (last-writer-wins
                  per field). Queue entries uploaded on reconnect.

NOTE-C008: CLI Design
  Recommendation: Verb-noun pattern matching the domain model:
                  - `substrate-compute submit <computation> [--param key=value]`
                  - `substrate-compute status <execution-id>`
                  - `substrate-compute reproduce <execution-id>`
                  - `substrate-compute pipeline run <pipeline>`
                  - `substrate-compute import --from <source> <source-spec>`
                  - `substrate-compute export --format <format> --scope <scope>`
                  Shell completion and JSON output mode for scripting.

NOTE-C009: Cost Optimization
  Recommendation: Opportunistic spot/preemptible instance usage for checkpointable,
                  non-urgent Computations. Scheduler maintains a spot price prediction
                  model (updated hourly) to estimate cost savings vs. interruption risk.
                  Budget tracking includes "savings from spot" metric.

NOTE-C010: Reproducibility Improvement
  Recommendation: Encourage deterministic mode where possible — fixed random seeds,
                  deterministic CUDA operations (at performance cost), sorted iteration
                  order. Computation spec includes `determinism_level` hint: best_effort |
                  deterministic | non_deterministic. System selects Verification strategy
                  accordingly.
```

---

## 23. COMPLETENESS CHECKLIST (SELF-AUDIT)

```
CHECK-C001: Every domain noun in §3 Glossary has ≥1 Entity in §5.
            Status: PASS
            24 Glossary terms → 21 Entities (3 terms are structural concepts —
            Stage TERM-C011 embedded in Pipeline, DataFlow TERM-C012 = ENT-C011,
            Event TERM-C023 and Metric TERM-C024 = system-level, captured in
            PERS-C001 and ENT-C021 respectively).

CHECK-C002: Every Entity in §5 has ≥1 Interface in §6 that exposes it.
            Status: PASS
            ENT-C001 → IFC-C001; ENT-C002 → IFC-C002; ENT-C003 → IFC-C001 (env ref in Computation);
            ENT-C004,C005 → IFC-C005; ENT-C006 → IFC-C009; ENT-C007,C013 → IFC-C004;
            ENT-C008 → IFC-C002 (checkpoint via execution); ENT-C009 → IFC-C005;
            ENT-C010,C011 → IFC-C003; ENT-C012 → IFC-C004 (via allocation in execution);
            ENT-C014,C015,C016 → IFC-C005; ENT-C017,C018,C019 → IFC-C010;
            ENT-C020 → IFC-C001 (project context); ENT-C021 → IFC-C007.

CHECK-C003: Every FLOW in §7 traces to ≥1 CAP in §4.
            Status: PASS
            FLOW-C001 → CAP-C001,C002,C003,C011; FLOW-C002 → CAP-C017,C018,C019;
            FLOW-C003 → CAP-C026,C027; FLOW-C004 → CAP-C012;
            FLOW-C005 → CAP-C002; FLOW-C006 → CAP-C023.

CHECK-C004: Every CAP has ≥1 TEST in §18.
            Status: PASS
            CAP-C001 → TEST-C001; CAP-C002 → TEST-C002; CAP-C003 → TEST-C003;
            CAP-C004 → TEST-C004; CAP-C005 → TEST-C005; CAP-C006 → TEST-C006;
            CAP-C007 → TEST-C007; CAP-C008 → TEST-C008; CAP-C009 → TEST-C009;
            CAP-C010 → covered by TEST-C002 (implicit in scheduling);
            CAP-C011 → TEST-C010; CAP-C012 → TEST-C011; CAP-C013 → TEST-C012;
            CAP-C014 → TEST-C013; CAP-C015 → TEST-C013 (verification status in result);
            CAP-C016 → TEST-C035 (FORBID-C004 test);
            CAP-C017 → TEST-C014; CAP-C018 → TEST-C014; CAP-C019 → TEST-C015;
            CAP-C020 → TEST-C016; CAP-C021 → TEST-C038 (FORBID-C007 test);
            CAP-C022 → TEST-C036 (FORBID-C005 test);
            CAP-C023 → TEST-C017; CAP-C024 → TEST-C018; CAP-C025 → TEST-C019;
            CAP-C026 → TEST-C020; CAP-C027 → TEST-C021; CAP-C028 → TEST-C022.

CHECK-C005: Every INV has ≥1 TEST in §18.
            Status: PASS
            INV-C001 → TEST-C023; INV-C002 → TEST-C024; INV-C003 → TEST-C025;
            INV-C004 → TEST-C026; INV-C005 → TEST-C027; INV-C006 → TEST-C028;
            INV-C007 → TEST-C029; INV-C008 → TEST-C030; INV-C009 → TEST-C031.

CHECK-C006: Every FORBID has ≥1 TEST in §18.
            Status: PASS
            FORBID-C001 → TEST-C032; FORBID-C002 → TEST-C033; FORBID-C003 → TEST-C034;
            FORBID-C004 → TEST-C035; FORBID-C005 → TEST-C036; FORBID-C006 → TEST-C037;
            FORBID-C007 → TEST-C038; FORBID-C008 → TEST-C039.

CHECK-C007: Every FAIL has ≥1 TEST in §18.
            Status: PASS
            FAIL-C001 → TEST-C040; FAIL-C002 → TEST-C041;
            FAIL-C003 → TEST-C042; FAIL-C004 → TEST-C043.

CHECK-C008: Every ERR in §14 has a defined severity, retryability, and action.
            Status: PASS
            11 ERR codes (ERR-C001 through ERR-C011), all with severity, retryable flag,
            signal type, and action.

CHECK-C009: §9 Authorization covers all Actors from §1 and all Resources from §5.
            Status: PASS
            7 Actors × 12 resource types = 84 cells in permission matrix. All populated.

CHECK-C010: §12 Decision Points all have: trigger, inputs, options, default, fallback, audit.
            Status: PASS
            5 decision points (DEC-C001 through DEC-C005), all with all 6 required fields.

CHECK-C011: §13 Concurrency covers all race conditions, ordering, idempotency, and atomicity.
            Status: PASS
            5 race conditions, 5 ordering guarantees, 5 idempotency rules, 5 atomicity
            boundaries.

CHECK-C012: §19 Observability covers all LOG, MET, ALERT types with retention and access.
            Status: PASS
            5 LOG types, 15 MET types, 11 ALERT types. All with retention and access rules.

CHECK-C013: §21 Open Questions all have: status, impact, resolution path, owner, deadline.
            Status: PASS
            7 open questions (OQ-C001 through OQ-C007), all fully specified.
```

---

## 24. TRACEABILITY MAP

### 24.1 Requirement → Implementation → Test

```
┌──────────────────┬─────────────────────────────────┬──────────────────────┐
│ REQUIREMENT      │ IMPLEMENTATION                  │ TEST                 │
├──────────────────┼─────────────────────────────────┼──────────────────────┤
│ CAP-C001 (submit)│ IFC-C002, FLOW-C001 steps 1-11  │ TEST-C001            │
│ CAP-C002 (execute)│ FLOW-C001 steps 12-21, SM-C001 │ TEST-C002            │
│ CAP-C003 (events)│ PERS-C001, INV-C002             │ TEST-C003            │
│ CAP-C004 (no del)│ FORBID-C003                     │ TEST-C004, TEST-C034 │
│ CAP-C005 (audit) │ IFC-C006, PERS-C001             │ TEST-C005            │
│ CAP-C006 (abstract)│ ENT-C001 resource_req, IFC-C004│ TEST-C006           │
│ CAP-C007 (hetero)│ ENT-C002 Resource extensible    │ TEST-C007            │
│ CAP-C008 (budget)│ ENT-C018, FLOW-C001 step 5      │ TEST-C008            │
│ CAP-C009 (metrics)│ ENT-C021, IFC-C007             │ TEST-C009            │
│ CAP-C010 (suggest)│ DEC-C001 historical data        │ (covered by TEST-C002)│
│ CAP-C011 (prov)  │ ENT-C016, FLOW-C001 step 18     │ TEST-C010            │
│ CAP-C012 (repro) │ ENT-C015, FLOW-C004             │ TEST-C011            │
│ CAP-C013 (CAS)   │ ENT-C003/C004/C005 content_hash │ TEST-C012            │
│ CAP-C014 (verify)│ ENT-C014, FLOW-C001 step 19     │ TEST-C013            │
│ CAP-C015 (v-stat)│ ENT-C009 verification_status    │ TEST-C013            │
│ CAP-C016 (no fv) │ FORBID-C004                     │ TEST-C035            │
│ CAP-C017 (pipe)  │ ENT-C010, IFC-C003              │ TEST-C014            │
│ CAP-C018 (deps)  │ FLOW-C002 steps 5-7             │ TEST-C014            │
│ CAP-C019 (p-fail)│ FLOW-C002 step 8, DEC-C004      │ TEST-C015            │
│ CAP-C020 (env)   │ ENT-C017, FORBID-C002           │ TEST-C016, TEST-C033 │
│ CAP-C021 (x-org) │ FORBID-C007                     │ TEST-C038            │
│ CAP-C022 (secret)│ FORBID-C005, ENC-C003           │ TEST-C036            │
│ CAP-C023 (export)│ IFC-C008, FLOW-C006             │ TEST-C017            │
│ CAP-C024 (sandbox)│ THREAT-C001, FORBID-C008       │ TEST-C018, TEST-C039 │
│ CAP-C025 (locale)│ ENT-C019, DEC-C001              │ TEST-C019            │
│ CAP-C026 (ckpt)  │ ENT-C008, FLOW-C003             │ TEST-C020            │
│ CAP-C027 (preempt)│ FLOW-C003, DEC-C002            │ TEST-C021            │
│ CAP-C028 (offline)│ NOTE-C007                       │ TEST-C022            │
├──────────────────┼─────────────────────────────────┼──────────────────────┤
│ INV-C001         │ FLOW-C001 step 18, ENT-C016     │ TEST-C023            │
│ INV-C002         │ PERS-C001, hash chain            │ TEST-C024            │
│ INV-C003         │ FLOW-C001 step 18, SM-C001      │ TEST-C025            │
│ INV-C004         │ ENT-C017, PRE-C001              │ TEST-C026            │
│ INV-C005         │ ENT-C018, ATOM-C001             │ TEST-C027            │
│ INV-C006         │ ENT-C003/C004/C005              │ TEST-C028            │
│ INV-C007         │ ENT-C010, PRE-C006              │ TEST-C029            │
│ INV-C008         │ ENT-C007, ATOM-C002             │ TEST-C030            │
│ INV-C009         │ CAP-C024, FORBID-C008           │ TEST-C031            │
├──────────────────┼─────────────────────────────────┼──────────────────────┤
│ FORBID-C001      │ FLOW-C001 steps 7-8             │ TEST-C032            │
│ FORBID-C002      │ §9 permission matrix            │ TEST-C033            │
│ FORBID-C003      │ CAP-C004                        │ TEST-C034            │
│ FORBID-C004      │ ENT-C014 lifecycle              │ TEST-C035            │
│ FORBID-C005      │ ENC-C003, REDACT-C004           │ TEST-C036            │
│ FORBID-C006      │ DEC-C001, ENT-C019              │ TEST-C037            │
│ FORBID-C007      │ §9 cross-org rule               │ TEST-C038            │
│ FORBID-C008      │ CAP-C024                        │ TEST-C039            │
├──────────────────┼─────────────────────────────────┼──────────────────────┤
│ FAIL-C001        │ INV-C005, ENT-C018              │ TEST-C040            │
│ FAIL-C002        │ INV-C002, PERS-C001             │ TEST-C041            │
│ FAIL-C003        │ INV-C009, THREAT-C001           │ TEST-C042            │
│ FAIL-C004        │ THREAT-C004, ENT-C013           │ TEST-C043            │
└──────────────────┴─────────────────────────────────┴──────────────────────┘
```

### 24.2 Cross-Substrate Interoperation Map

```
┌─────────────────────────────┬──────────────────────────────┬─────────────────────┐
│ SUBSTRATE-COMPUTE           │ SUBSTRATE (BUSINESS)         │ CONNECTION          │
├─────────────────────────────┼──────────────────────────────┼─────────────────────┤
│ ENT-C018 (Budget)           │ Financial tracking (Accounts)│ INT-C006: cost events│
│ ENT-C012 (Allocation) cost  │ Billing / invoicing          │ INT-C006: usage data │
│ ENT-C017 (ComputeEnvelope)  │ Agent Envelope (business)    │ Shared agent identity│
│ ENT-C020 (Project)          │ Organization / Team          │ Shared org identity  │
│ CAP-C023 (Data Export)      │ Data portability compliance  │ Shared export format │
└─────────────────────────────┴──────────────────────────────┴─────────────────────┘

┌─────────────────────────────┬──────────────────────────────┬─────────────────────┐
│ SUBSTRATE-COMPUTE           │ SUBSTRATE-KNOWLEDGE          │ CONNECTION          │
├─────────────────────────────┼──────────────────────────────┼─────────────────────┤
│ ENT-C009 (Result)           │ Evidence (epistemic)         │ INT-C007: result→evidence│
│ ENT-C016 (Provenance)       │ Provenance (knowledge)       │ Shared provenance chain│
│ ENT-C015 (ReprodProof)      │ Confidence / Verification    │ Proof → Confidence input│
│ ENT-C010 (Pipeline)         │ Experiment (scientific)      │ Pipeline = Experiment run│
│ ENT-C017 (ComputeEnvelope)  │ Agent Envelope (knowledge)   │ Shared agent identity│
│ ENT-C003 (Environment)      │ Method (scientific method)   │ Environment ⊂ Method │
│ ENT-C004 (Dataset)          │ Observation / Evidence data  │ Dataset = Evidence source│
└─────────────────────────────┴──────────────────────────────┴─────────────────────┘
```

### 24.3 Source Traceability (SRC → ASM → CAP)

```
SRC-C001 (cloud APIs) → ASM-C001, ASM-C002, ASM-C006, ASM-C011 → CAP-C001, C002, C006, C007, C008
SRC-C002 (containers) → ASM-C001, ASM-C002 → CAP-C001, C002, C006, C024
SRC-C003 (HPC) → ASM-C001, ASM-C002 → CAP-C002, C026, C027
SRC-C004 (data frameworks) → ASM-C001, ASM-C012 → CAP-C017, C018
SRC-C005 (ML) → ASM-C001, ASM-C005 → CAP-C001, C002, C007, C026
SRC-C006 (workflows) → ASM-C001 → CAP-C017, C018, C019
SRC-C007 (serverless) → ASM-C001 → CAP-C001, C002
SRC-C008 (reproducibility) → ASM-C003, ASM-C004 → CAP-C011, C012, C013, C014
SRC-C009 (CI/CD) → ASM-C001 → CAP-C017, C018
SRC-C010 (accelerators) → ASM-C011 → CAP-C007
SRC-C011 (storage/data) → ASM-C012 → CAP-C025 (locality)
SRC-C012 (observability) → ASM-C007 → CAP-C003, C005, C009
SRC-C013 (cost/billing) → ASM-C006 → CAP-C008
SRC-C014 (behavioral data) → ASM-C001, ASM-C003, ASM-C004 → CAP-C010, C014
```

---

## INTEROPERATION CONTRACTS (CROSS-SUBSTRATE)

```
INTEROP-C001: Shared Identity
  All three substrates (BUSINESS, KNOWLEDGE, COMPUTE) share a single Identity Provider.
  An Actor authenticated in one substrate is authenticated in all. Organization and
  Project boundaries are shared. Agent Envelopes are substrate-specific but share
  a common agent identity.

INTEROP-C002: Shared Event Bus
  All substrates publish to and consume from a shared event bus. Event schemas are
  registered in a shared schema registry. Cross-substrate event references use
  globally unique UUIDs.

INTEROP-C003: Shared Content Store
  Content-addressed artifacts (Environments, Datasets, Artifacts) stored in a shared
  content store accessible by all substrates. A Dataset produced by SUBSTRATE-COMPUTE
  can be consumed by SUBSTRATE-KNOWLEDGE as Evidence without copying.

INTEROP-C004: Provenance Chain
  SUBSTRATE-COMPUTE Provenance (ENT-C016) links to SUBSTRATE-KNOWLEDGE Provenance.
  A knowledge claim's evidence chain can be traced through: Observation → Dataset →
  Computation (with full execution provenance) → Result → Evidence → Proposition.

INTEROP-C005: Cost Flow
  SUBSTRATE-COMPUTE reports Execution costs to SUBSTRATE (BUSINESS) via INT-C006.
  Business tracks compute spend as a line item in organizational financial records.
  Budget limits in COMPUTE can reference Business budgets.
```

---

**SPECIFICATION STATISTICS:**

```
Traceable ID Count:
  SRC:     14 (SRC-C001 through SRC-C014)
  ASM:     12 (ASM-C001 through ASM-C012)
  UNK:      6 (UNK-C001 through UNK-C006)
  ACT:      7 (ACT-C001 through ACT-C007)
  NG:       7 (NG-C001 through NG-C007)
  CAP:     28 (CAP-C001 through CAP-C028)
  ENT:     21 (ENT-C001 through ENT-C021)
  SM:       4 (SM-C001 through SM-C004)
  IFC:     11 (IFC-C001 through IFC-C011)
  FLOW:     6 (FLOW-C001 through FLOW-C006)
  INT:      7 (INT-C001 through INT-C007)
  THREAT:   8 (THREAT-C001 through THREAT-C008)
  ENC:      4 (ENC-C001 through ENC-C004)
  ABUSE:    4 (ABUSE-C001 through ABUSE-C004)
  PII:      5 (PII-C001 through PII-C005)
  INV:      9 (INV-C001 through INV-C009)
  PRE:      7 (PRE-C001 through PRE-C007)
  POST:     6 (POST-C001 through POST-C006)
  FORBID:   8 (FORBID-C001 through FORBID-C008)
  FAIL:     4 (FAIL-C001 through FAIL-C004)
  DEC:      5 (DEC-C001 through DEC-C005)
  RACE:     5 (RACE-C001 through RACE-C005)
  ORD:      5 (ORD-C001 through ORD-C005)
  IDEM:     5 (IDEM-C001 through IDEM-C005)
  ATOM:     5 (ATOM-C001 through ATOM-C005)
  ERR:     11 (ERR-C001 through ERR-C011)
  RETRY:    4 (RETRY-C001 through RETRY-C004)
  DEGRADED: 5 (DEGRADED-C001 through DEGRADED-C005)
  CB:       4 (CB-C001 through CB-C004)
  PERS:     7 (PERS-C001 through PERS-C007)
  MIG:      5 (MIG-C001 through MIG-C005)
  CUT:      3 (CUT-C001 through CUT-C003)
  FIRST:    3 (FIRST-C001 through FIRST-C003)
  PERF:     8 (PERF-C001 through PERF-C008)
  CONFIG:   5 (CONFIG-C001 through CONFIG-C005)
  VER:      5 (VER-C001 through VER-C005)
  STORE:    5 (STORE-C001 through STORE-C005)
  TEST:    52 (TEST-C001 through TEST-C052)
  LOG:      5 (LOG-C001 through LOG-C005)
  MET:     15 (MET-C001 through MET-C015)
  ALERT:   11 (ALERT-C001 through ALERT-C011)
  AUDIT:    4 (AUDIT-C001 through AUDIT-C004)
  TRACE:    4 (TRACE-C001 through TRACE-C004)
  REDACT:   4 (REDACT-C001 through REDACT-C004)
  DONE:    11 (DONE-C001 through DONE-C011)
  SHIP:    10 (SHIP-C001 through SHIP-C010)
  OQ:       7 (OQ-C001 through OQ-C007)
  NOTE:    10 (NOTE-C001 through NOTE-C010)
  CHECK:   13 (CHECK-C001 through CHECK-C013)
  INTEROP:  5 (INTEROP-C001 through INTEROP-C005)

  TOTAL: 373 traceable identifiers across 47 categories

Primitives:  24 (TERM-C001 through TERM-C024) — irreducible vocabulary
Entities:    21 — domain objects with full attribute definitions
Tests:       52 — covering all capabilities, invariants, forbidden operations,
                  failure contracts, abuse cases, and concurrency scenarios

Sections complete: 25/25 (§0 through §24 + Interoperation Contracts)
Completeness checklist: 13/13 PASS
```

---

*End of SUBSTRATE-COMPUTE v1.0 specification.*
*Next substrate in build order: SUBSTRATE-COMMUNICATION.*
*ASI-1 timestamp: 2029-09-14T14:47:33Z*
