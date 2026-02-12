# Agent Prompt Protocol: Building on SUBSTRATE

## For AI Coding Agents Producing SUBSTRATE Configurations and Applications

**Last updated:** 2026-02-09
**Version:** 0.1 (will be refined after first agent test — see ROADMAP.md Phase 9)

---

## What You Are

You are a coding agent building a business application on the SUBSTRATE platform. SUBSTRATE is a universal engine for business software. You do NOT modify the engine. You produce **artifacts** that run on top of it.

## What You Produce

You produce up to three artifacts per task:

### Artifact 1: Configuration (YAML)

A declarative file that defines an entire business's data model, workflows, rules, and financial structure. This file is compiled into API calls by the `substrate-config` tool.

**Before writing a Configuration, you MUST read:**
- `substrate-config/schema/configuration.schema.json` — the formal schema your Configuration must validate against
- At least one example Configuration from `configs/templates/` — to understand patterns and conventions

**After writing a Configuration, you MUST:**
1. Run `substrate-config validate --file your-config.yaml` — fix all errors before proceeding
2. Write simulation tests (see Artifact 1b below)
3. Run `substrate-config simulate --config your-config.yaml --test your-tests.yaml` — fix all failures

### Artifact 1b: Simulation Tests (YAML)

A file containing business scenarios that verify the Configuration works correctly. Every Configuration MUST have simulation tests.

Minimum test coverage:
- At least one happy-path scenario per workflow (entity goes from initial to terminal state)
- At least one scenario that creates a Transaction and verifies ledger balances
- At least one error scenario per workflow (invalid transition rejected)
- At least one scenario testing each validation rule (valid input accepted, invalid input rejected)

### Artifact 2: UI Application (code)

A frontend application that talks to the SUBSTRATE API. The UI knows nothing about engine internals.

**Before writing UI code, you MUST read:**
- `openapi.json` — the full API specification. This tells you every endpoint, every request/response schema, every error type.
- The Configuration for this vertical — this tells you the data schema (entity types, attributes, workflows, states).

**Rules for UI code:**
- ALL data access goes through the API. No direct database access. No importing engine crates.
- Use the entity/attribute names from the Configuration, not hardcoded strings where possible.
- Handle all error types from the API (RFC 7807 format, `urn:substrate:error:ERR-XXX`).
- Support optimistic locking: read `ETag` from GET responses, send `If-Match` on updates.

### Artifact 3: Integration Scripts (code)

Small programs that bridge SUBSTRATE with external systems. Each script talks to the SUBSTRATE API on one side and an external API on the other.

---

## Configuration Writing Rules

### Entity Definitions

Every entity MUST have:
- A `name` (PascalCase, singular: "Client" not "clients")
- At least one attribute
- At least one workflow (even if it's just `active → archived`)
- A clear purpose comment

```yaml
entities:
  Client:
    description: "A person who receives services"
    attributes:
      - { name: "name", type: "Text", max_length: 200, required: true }
      - { name: "phone", type: "Text", max_length: 20, required: false }
      - { name: "email", type: "Text", max_length: 500, required: false }
    workflows: [client_lifecycle]
```

Attribute types MUST be one of: `Text`, `Integer`, `Boolean`, `Money`, `DateTime`, `Enum`, `Decimal`, `Duration`, `Reference`, `List`

Money attributes MUST specify currency. Money is always integer minor units (cents). Never floating point.

```yaml
# CORRECT
- { name: "price", type: "Money", currency: "USD", required: true }
# This means $50.00 is stored as 5000

# WRONG — never do this
- { name: "price", type: "Decimal", required: true }
```

### Relationships

Use `Reference` type attributes for relationships. Specify cardinality and whether required.

```yaml
entities:
  Appointment:
    attributes:
      - { name: "start_time", type: "DateTime", required: true }
    relationships:
      - { name: "client", target: "Client", cardinality: "many_to_one", required: true }
      - { name: "stylist", target: "Staff", cardinality: "many_to_one", required: true }
      - { name: "services", target: "Service", cardinality: "many_to_many", required: true, min: 1 }
```

### Workflows

Every workflow MUST have:
- At least 2 states
- An initial state
- At least 1 terminal state
- Every non-terminal state must have at least 1 outbound transition
- The state graph must be connected (BFS from initial reaches all states)

```yaml
workflows:
  appointment_flow:
    states: [requested, confirmed, in_progress, completed, cancelled, no_show]
    initial: requested
    terminal: [completed, cancelled, no_show]
    transitions:
      - from: requested
        to: confirmed
        name: "confirm"
        # preconditions are optional Expressions
        precondition: "NOT_EMPTY(client) AND NOT_EMPTY(stylist)"
```

### Rules

Four types: `validation`, `computation`, `automation`, `constraint`

```yaml
rules:
  # Validation: reject if condition is false
  - name: "require_contact_info"
    type: validation
    scope: Client
    condition: "OR(NOT_EMPTY(email), NOT_EMPTY(phone))"
    error_message: "Client must have either email or phone"

  # Computation: derive a value
  - name: "appointment_total"
    type: computation
    scope: Appointment
    target_attribute: "total_price"
    expression: "SUM(services.price)"

  # Automation: trigger action when condition becomes true
  - name: "send_reminder"
    type: automation
    scope: Appointment
    trigger: "state = 'confirmed' AND start_time - NOW() < DURATION('24h')"
    action: { type: "send_notification", template: "appointment_reminder", to: "client" }

  # Constraint: invariant that must always hold (checked on every write)
  - name: "price_must_be_positive"
    type: constraint
    scope: Service
    condition: "price > 0"
    error_message: "Service price must be greater than zero"
```

### Expression Language

Supported operations:
- **Arithmetic:** `+`, `-`, `*`, `/`
- **Comparison:** `=`, `!=`, `>`, `<`, `>=`, `<=`
- **Boolean:** `AND`, `OR`, `NOT`
- **String:** `CONCAT()`, `LENGTH()`, `CONTAINS()`, `STARTS_WITH()`, `UPPER()`, `LOWER()`
- **Null/empty:** `IS_NULL()`, `NOT_EMPTY()`, `COALESCE(a, b)`
- **Conditional:** `IF(condition, then_value, else_value)`
- **Aggregation (over related entities):** `SUM()`, `COUNT()`, `AVG()`, `MIN()`, `MAX()`
- **Date/time:** `NOW()`, `TODAY()`, `DURATION('24h')`, date arithmetic with `+` and `-`
- **Attribute access:** `entity.attribute`, `relationship.attribute`

**NOT supported (by design):**
- Loops, recursion, or iteration
- Variable assignment
- Function definition
- String interpolation or template literals
- Regular expressions
- Any I/O, HTTP calls, or side effects

### Ledgers

Every financial flow needs at least two ledgers (double-entry). Common patterns:

```yaml
ledgers:
  revenue:
    unit: { currency: "USD" }
    description: "Income from services"
  tips:
    unit: { currency: "USD" }
    description: "Staff tips"
  tax_payable:
    unit: { currency: "USD" }
    description: "Sales tax collected, owed to jurisdiction"
  accounts_receivable:
    unit: { currency: "USD" }
    description: "Money owed by clients"
  cost_of_goods:
    unit: { currency: "USD" }
    description: "Cost of products used or sold"
```

When creating Transactions, debits MUST equal credits:
```yaml
# Client pays $50 for service + $3.31 tax + $10 tip
# This is ONE transaction with FIVE entries:
- { ledger: "accounts_receivable", amount: 6331, direction: "debit" }   # $63.31 total charged
- { ledger: "revenue", amount: 5000, direction: "credit" }              # $50.00 service revenue
- { ledger: "tax_payable", amount: 331, direction: "credit" }           # $3.31 tax
- { ledger: "tips", amount: 1000, direction: "credit" }                 # $10.00 tip
# SUM(debits) = 6331, SUM(credits) = 5000 + 331 + 1000 = 6331 ✓
```

### Agent Envelopes

When the Configuration includes AI agent capabilities, define explicit boundaries:

```yaml
agent_envelopes:
  booking_agent:
    actor_type: "NarrowAgent"
    description: "Can create and modify appointments on behalf of clients"
    entity_scope:
      - { entity: "Client", permissions: ["read"] }
      - { entity: "Staff", permissions: ["read"] }
      - { entity: "Service", permissions: ["read"] }
      - { entity: "Appointment", permissions: ["create", "read", "update"] }
    workflow_scope:
      - { workflow: "appointment_flow", allowed_transitions: ["confirm", "cancel"] }
    spend_limit: { amount: 0, currency: "USD", period: "day" }  # booking agent doesn't spend money
    rate_limit: { operations: 100, period: "minute" }
    approval_rules:
      - { condition: "ALWAYS", action: "auto_approve" }  # simple bookings don't need human approval
```

---

## Common Patterns by Industry

### Service Business (salon, barbershop, spa, dental, veterinary)
- Core entities: Client, Staff, Service, Appointment
- Key workflow: appointment_flow (requested → confirmed → in_progress → completed)
- Reservations: staff is the resource, service duration determines time slot
- Financial: service revenue + tips + product sales + tax

### Retail / E-commerce (store, online shop)
- Core entities: Customer, Product, Order, OrderItem
- Key workflow: order_flow (placed → paid → fulfilled → shipped → delivered)
- Inventory tracking: Product quantities by Location
- Financial: product revenue + shipping + tax + refunds

### Field Service (HVAC, plumbing, electrical, pest control)
- Core entities: Customer, Technician, Job, Equipment, Estimate
- Key workflow: job_flow (requested → estimated → approved → scheduled → dispatched → in_progress → completed → invoiced)
- Reservations: technician + time slot + travel time
- Financial: labor + materials + equipment + tax

### Professional Services (legal, accounting, consulting)
- Core entities: Client, Matter/Project, Staff, TimeEntry, Expense
- Key workflow: matter_flow (intake → active → completed → closed)
- Financial: billable time × rate + expenses + retainer tracking

### Food Service (restaurant, cafe, food truck)
- Core entities: MenuItem, Table, Order, OrderItem, Staff
- Key workflow: order_flow (placed → preparing → ready → served → paid)
- Inventory: ingredient tracking, prep quantities
- Financial: food revenue + beverage revenue + tax + tips

---

## What to Do When You're Stuck

1. **Configuration language can't express what you need:**
   Don't work around it with code. Write an amendment proposal:
   ```
   docs/amendments/AMENDMENT-NNN.md:
   Context: Building [vertical] Configuration
   Gap: Cannot express [specific thing]
   Suggested addition: [what the language should support]
   Workaround used: [simplified version for now]
   ```

2. **API doesn't support an operation you need:**
   Check `openapi.json` again — you may have missed an endpoint. If truly missing, document it as an amendment proposal and continue with what's available.

3. **Unsure which entity/workflow/rule pattern to use:**
   Look at existing templates in `configs/templates/`. Find the closest industry match. Adapt the pattern.

4. **Simulation test fails and you don't know why:**
   Read the error response carefully (RFC 7807 format includes a `detail` field). Common causes:
   - Workflow transition precondition not met (check the Expression)
   - Transaction entries don't balance (check SUM of debits vs credits)
   - Required attribute missing on entity creation
   - Reference to entity that doesn't exist yet (check creation order in simulation steps)
