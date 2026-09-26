# Local validation record

The authoring workspace does not have Docker or a Lean/Lake installation, so the full Harbor oracle and no-op runs cannot be executed locally here.

Static checks performed:
- required bundle files are present;
- the artifact path is absolute and declared in task.toml;
- the verifier is configured as a separate offline environment;
- reward writing is guarded by an EXIT trap;
- tests do not depend on solution/ or authoring/;
- the verifier compiles the submitted file in a clean Mathlib project and audits axiom dependencies.

The reference proof was revised to use explicit Mathlib theorem arguments and less fragile coefficient/cardinality rewrites. The platform's independent environment must still perform the authoritative oracle and no-op runs before submission is considered validated.
