import Lean
import Qed.Lang

namespace Qed.Cloud

/-! ## `deploy` Block Surface Syntax (`Qed.Cloud.Syntax`) -/

declare_syntax_cat deployClause
declare_syntax_cat deployPreviewClause

section DeployParsers
open Lean Parser Qed.Lang

private def kwP (kw : Name) (p : Parser) : Parser :=
  withPosition (atomic (identEq kw) >> p)

def deployUnitLit : Parser :=
  node `Qed.Cloud.unitLit (numLit >> checkNoWsBefore "expected unit suffix without space" >> ident)

@[deployPreviewClause_parser] def deployPreviewOnPrClause : Parser := leading_parser kwP `on_pr (identEq `true <|> identEq `false)
@[deployPreviewClause_parser] def deployPreviewSubdomainClause : Parser := leading_parser kwP `subdomain strLit
@[deployPreviewClause_parser] def deployPreviewDomainClause : Parser := leading_parser kwP `domain strLit
@[deployPreviewClause_parser] def deployPreviewProtectionClause : Parser := leading_parser kwP `protection (identEq `team_only <|> identEq `anyone <|> symbol "public")
@[deployPreviewClause_parser] def deployPreviewTtlClause : Parser := leading_parser kwP `ttl deployUnitLit

@[deployClause_parser] def deployAppClause : Parser := leading_parser kwP `app ident
@[deployClause_parser] def deployRegionsClause : Parser := leading_parser kwP `regions ("[" >> sepBy1 ident "," >> "]")
@[deployClause_parser] def deployDomainClause : Parser := leading_parser kwP `domain strLit
@[deployClause_parser] def deployComputeClause : Parser := leading_parser kwP `compute ident
@[deployClause_parser] def deployTimeoutClause : Parser := leading_parser kwP `timeout deployUnitLit
@[deployClause_parser] def deployPreviewBlockClause : Parser := leading_parser
  kwP `preview (":" >> checkColGt "expected indented `preview:` clauses" >> many1Indent (categoryParser `deployPreviewClause 0))
@[deployClause_parser] def deployInvClause : Parser := leading_parser
  withPosition ("invariant " >> ident >> ":" >> sepBy1 (categoryParser `qedExpr 0) ",")

@[command_parser] def deployCmd : Parser := leading_parser
  withPosition ("deploy " >> ident >> ":" >> checkColGt "expected indented `deploy` clauses" >> many1Indent (categoryParser `deployClause 0))

end DeployParsers
end Qed.Cloud
