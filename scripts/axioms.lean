import Qed
import Examples.Counter
import Examples.Booking
import Examples.Chat
import Examples.Template
import Examples.Live
import Examples.Socket

#print axioms counterSafe
#print axioms Booking.bookedNeedsToday
#print axioms TemplateDemo.idsBelowNext
#print axioms Live.nonNegative
#print axioms Socket.composerOnlyWhenOnline
#print axioms Chat.streamSafe
#print axioms Qed.diff_apply
#print axioms Qed.diffChildren_apply
#print axioms Qed.applyChildrenTR_toList
#print axioms Qed.renderNode_eq_renderNodeTR
#print axioms Qed.renderChildren_eq_renderChildrenFast
#print axioms Qed.applyValues_render
#print axioms Qed.patch_render
#print axioms Qed.View.render_showIf
#print axioms Qed.View.stable_showIf_hidden
#print axioms Qed.View.collectShape_showIf
#print axioms Qed.View.collectDyn_showIf
#print axioms Qed.View.renderSig_showIf
#print axioms Qed.parse_depth_le
#print axioms Qed.Route.round_trip
#print axioms Qed.TypedRoute.round_trip
#print axioms Qed.Demo.Signup.canSubmit_iff
#print axioms Qed.parse_render
#print axioms Qed.Json.render_eq_renderFast
#print axioms Qed.LawfulJson.parse_render_toJson
#print axioms Qed.hydrate_coalesce
