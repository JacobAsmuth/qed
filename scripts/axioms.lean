import Qed
import Qed.Proofs.DomEquiv
import Js.Proofs
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

-- XSS, URL Scheme & HTML5 Serialization Closure (#3b)
#print axioms Qed.Url.isSafe
#print axioms Qed.containsCloseSeq_escapeRawText
#print axioms Qed.encodeSeg_safe
#print axioms Qed.Router.isSafeUrl_toURL
#print axioms Qed.ToHref.isSafeUrl_toHref
#print axioms Qed.escapeHtml_no_markup_or_quote
#print axioms Qed.sanitizeKey_safe
#print axioms Qed.renderAttr_blocks_inline_handler
#print axioms Qed.renderAttr_blocks_srcdoc
#print axioms Qed.renderAttr_blocks_unsafe_url
#print axioms Qed.safeScriptSrc_no_markup_or_quote

-- Imperative DOM Reconciler, Hydration, Memo, Key Disambiguation & SSR Equivalence (#2)
#print axioms Qed.disambiguateKeys_nodup
#print axioms Qed.disambiguateKeys_size
#print axioms Qed.disambiguateKeys_of_nodup
#print axioms Qed.V.render_memo
#print axioms Qed.buildDomM_spec
#print axioms Qed.specDom_applyPatch_diff
#print axioms Qed.w3cInsertBefore_step
#print axioms Qed.w3cReconcileKeyed_eq
#print axioms Qed.hydrateTextRun_equiv
#print axioms Qed.hydrateDomM_ownsChildren_element
#print axioms Qed.patchViewM_memo_hit
#print axioms Qed.patchViewM_dyn_spec
#print axioms Qed.forEach_disambiguated_keys_nodup
#print axioms Qed.App.ssr_rehydrate_equiv

-- Typed JS Backend & Runtime Semantics Preservation (#3c)
#print axioms Js.Proofs.jsTag_lowerCtor
#print axioms Js.Proofs.fieldProj_lowerCtor
#print axioms Js.Proofs.rtApp_under_compose
#print axioms Js.Proofs.rtApp_exact_equiv
#print axioms Js.Proofs.rtApp_over_equiv
#print axioms Js.Proofs.lowerBody_jdecl_nonrec_shape
#print axioms Js.Proofs.jdecl_inline_early_return_equiv
#print axioms Js.Proofs.jdecl_inline_jump_equiv
#print axioms Js.Proofs.lowerBody_selfTail_shape
#print axioms Js.Proofs.tailContinue_staged_assign_sound
#print axioms Js.Proofs.directLoop_equiv
#print axioms Js.Proofs.trampoline_equiv
#print axioms Js.Proofs.CowHeap.cowUset_obs_equiv
#print axioms Js.Proofs.CowHeap.cowPush_obs_equiv
#print axioms Js.Proofs.CowHeap.refMark_creates_snapshot
#print axioms Js.Proofs.CowHeap.SnapshotValid_cowUset
#print axioms Js.Proofs.CowHeap.SnapshotValid_cowPush
#print axioms Js.Proofs.CowHeap.SnapshotValid_refMark
#print axioms Js.Proofs.CowHeap.refMark_snapshot_sound
#print axioms Js.Proofs.memo_thunk_obs_equiv
