import Lean
import Qed.Lang

namespace Qed.Cloud

/-! ## `deploy` Block Surface Syntax (`Qed.Cloud.Syntax`)
    Vercel-style Qed grammar for Cloud Run deployments: high-level `compute` presets
    (`standard | performance | large | xlarge`), duration unit tokens (`60s`, `5m`, `7d`),
    and inline auto-proved `invariant`s. Low-level container counts, CPU/memory ratios,
    and concurrency are derived and proved automatically by `compileInfra`. -/

declare_syntax_cat deployClause
declare_syntax_cat deployPreviewClause

section DeployParsers
open Lean Parser Qed.Lang

/-- Dedicated duration unit literal such as `60s`, `5m`, `1h`, `7d`. -/
def deployUnitLit : Parser :=
  node `Qed.Cloud.unitLit (numLit >> checkNoWsBefore "expected unit suffix without space" >> ident)

-- `preview:` sub-clauses
@[deployPreviewClause_parser] def deployPreviewOnPrClause : Parser := leading_parser
  withPosition (atomic (identEq `on_pr) >> (identEq `true <|> identEq `false))

@[deployPreviewClause_parser] def deployPreviewSubdomainClause : Parser := leading_parser
  withPosition (atomic (identEq `subdomain) >> strLit)

@[deployPreviewClause_parser] def deployPreviewDomainClause : Parser := leading_parser
  withPosition (atomic (identEq `domain) >> strLit)

@[deployPreviewClause_parser] def deployPreviewProtectionClause : Parser := leading_parser
  withPosition (atomic (identEq `protection) >> (identEq `team_only <|> identEq `anyone <|> symbol "public"))

@[deployPreviewClause_parser] def deployPreviewTtlClause : Parser := leading_parser
  withPosition (atomic (identEq `ttl) >> deployUnitLit)

-- Top-level `deploy` clauses
@[deployClause_parser] def deployAppClause : Parser := leading_parser
  withPosition (atomic (identEq `app) >> ident)

@[deployClause_parser] def deployRegionsClause : Parser := leading_parser
  withPosition (atomic (identEq `regions) >> "[" >> sepBy1 ident "," >> "]")

@[deployClause_parser] def deployDomainClause : Parser := leading_parser
  withPosition (atomic (identEq `domain) >> strLit)

@[deployClause_parser] def deployComputeClause : Parser := leading_parser
  withPosition (atomic (identEq `compute) >> ident)

@[deployClause_parser] def deployTimeoutClause : Parser := leading_parser
  withPosition (atomic (identEq `timeout) >> deployUnitLit)

@[deployClause_parser] def deployPreviewBlockClause : Parser := leading_parser
  withPosition (
    atomic (identEq `preview) >> ":" >>
    checkColGt "expected indented `preview:` clauses" >>
    many1Indent (categoryParser `deployPreviewClause 0))

@[deployClause_parser] def deployInvClause : Parser := leading_parser
  withPosition (
    "invariant " >> ident >> ":" >> sepBy1 (categoryParser `qedExpr 0) ",")

@[command_parser] def deployCmd : Parser := leading_parser
  withPosition (
    "deploy " >> ident >> ":" >>
    checkColGt "expected indented `deploy` clauses" >>
    many1Indent (categoryParser `deployClause 0))

end DeployParsers

end Qed.Cloud
