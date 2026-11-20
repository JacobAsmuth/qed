import Qed
import Qed.Server.Native
import Qed.Proofs.DomArena
import Qed.Proofs.ViewPatch
import Qed.Proofs.KeyedReconcile
import Qed.Proofs.Hydration
import Js.Proofs
import Examples.Counter
import Examples.Todo
import Examples.Signup
import Examples.Chat
import Examples.Bookshelf
import Examples.CloudBooks
import Examples.LiveRoom

#print axioms Counter.counterSafe
#print axioms Todo.Row.rowSafe
#print axioms Todo.Row.rowStyled
#print axioms Todo.rowsSafe
#print axioms Todo.rowsStyled
#print axioms Account.canSubmit_iff
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

-- Verified Binary Protocol Buffers, Full-Stack SSR/RPC & Multi-Core Server Linearizability
#print axioms Qed.Proto.decodeFrameList_append
#print axioms Qed.Proto.cursor_strictly_advances
#print axioms Qed.Proto.skipUnknown_preserves_lookup_suffix
#print axioms Qed.Proto.skipUnknown_preserves_repeated_suffix
#print axioms Qed.Proto.decodeHex_encodeHex
#print axioms Qed.Proto.decode_encode
#print axioms Qed.rpc_wire_roundtrip
#print axioms Qed.fullstack_ssr_rpc_equiv
#print axioms Qed.Server.header_no_crlf
#print axioms Qed.Server.Net.base64UrlEncode_safe
#print axioms Qed.Server.Net.isBlockedIpBytes_loopback_v4
#print axioms Qed.Server.Net.isBlockedIpBytes_metadata_v4
#print axioms Qed.Server.Net.isBlockedIpBytes_rfc1918_10
#print axioms Qed.Server.Net.isBlockedIpBytes_testnet_v4
#print axioms Qed.Server.Net.isBlockedIpBytes_benchmark_v4
#print axioms Qed.Server.Net.isBlockedIpBytes_loopback_v6
#print axioms Qed.Server.Net.isBlockedIpBytes_v4mapped_metadata
#print axioms Qed.Server.Net.isBlockedIpBytes_nat64_metadata
#print axioms Qed.Server.Net.isBlockedIpBytes_nat64_local_v6
#print axioms Qed.Server.Net.isBlockedIpBytes_6to4_v6
#print axioms Qed.Server.Net.isBlockedIpBytes_teredo_v6
#print axioms Qed.Server.Net.isBlockedIpBytes_badLen
#print axioms Qed.Server.Net.parseHttpUrl_no_fragment
#print axioms Qed.Server.Http.parseRequestHead_rejects_nul
#print axioms Qed.Server.Http.parseOneHeaderLine_rejects_bad_name
#print axioms Qed.Server.Http.parseRequestHead_http11_has_host
#print axioms Qed.Server.Http.parseRequestHead_contentLen_le
#print axioms Qed.Server.Http.safeContentType_no_crlf
#print axioms Qed.Server.Http.isContentHashedAsset_hashed
#print axioms Qed.Server.Http.isContentHashedAsset_plain
#print axioms Qed.Server.Http.classifyStaticPath_rejects_dotdot
#print axioms Qed.Server.Http.sha1_size
#print axioms Qed.Server.Http.base64Encode_rfc6455_accept
#print axioms Qed.Server.Http.decodeWsFrame_rejects_unmasked
#print axioms Qed.Server.Http.decodeWsFrame_rejects_rsv
#print axioms Qed.Server.external_url_preserves_origin
#print axioms Qed.Server.readOnly_preserves_state
#print axioms Qed.Server.concurrent_schedule_preserves_inv
#print axioms Qed.Server.safeIO_bind_preservesStepRel
#print axioms CloudBooks.Catalog.inv_init
#print axioms CloudBooks.Catalog.list_readOnly
#print axioms CloudBooks.Catalog.findAt_readOnly
#print axioms CloudBooks.Catalog.cover_inv
#print axioms CloudBooks.Catalog.order_inv
#print axioms CloudBooks.Catalog.order_twoInv0
#print axioms CloudBooks.Catalog.order_mutInv0
#print axioms CloudBooks.Catalog.addBook_inv
#print axioms CloudBooks.Catalog.addBook_twoInv0
#print axioms CloudBooks.Catalog.addBook_mutInv0
#print axioms CloudBooks.Catalog.concurrent_linearizable

-- 10 Formal Proof Extensions: Diff, Resource, Router, Style, Render, Local, Ssr, Proofs/*, Js.Proofs
#print axioms Qed.validatedKeyIndex_spec
#print axioms Qed.diff_keyed_reuses
#print axioms Qed.diff_positional_reuses

#print axioms Qed.Cached.put_stale_preserves_state
#print axioms Qed.Cached.put_matching_updates_state
#print axioms Qed.Cached.put_non_ok_preserves_seen
#print axioms Qed.Cached.lookup_put_ok
#print axioms Qed.Cached.lookup_put_ok_sound
#print axioms Qed.Cached.put_seen_length_le
#print axioms Qed.Query.wrap_preserves_inv
#print axioms Qed.Query.wrap_noop_when_keys_unchanged

#print axioms Qed.decodeSeg_encodeSeg
#print axioms Qed.Router.fromURL_toURL
#print axioms Qed.Router.canonical_reparse

#print axioms Qed.sanitizeKey_of_safe
#print axioms Qed.renderAttr_valid_attr
#print axioms Qed.renderAttr_valid_flag
#print axioms Qed.renderAttr_valid_on
#print axioms Qed.renderAttr_no_angle_brackets
#print axioms Qed.renderAttrs_no_angle_brackets
#print axioms Qed.Html.validIn_everyElementSafe
#print axioms Qed.Html.valid_everyElementSafe

#print axioms Qed.sanitizeCssAtom_safe
#print axioms Qed.sanitizeCssSelector_safe
#print axioms Qed.Item.render_no_lt
#print axioms Qed.Item.renderList_no_lt
#print axioms Qed.Item.render_no_closeSeq
#print axioms Qed.Item.renderList_no_closeSeq
#print axioms Qed.Style.rule_no_lt

#print axioms Qed.LocalDef.valid_viewForProps
#print axioms Qed.LocalDef.dedupe_mem
#print axioms Qed.LocalDef.dedupe_ids_nodup
#print axioms Qed.LocalDef.decode_toJson_eq
#print axioms Qed.LocalDef.of_view_roundtrip
#print axioms Qed.LocalDef.ofProps_view_roundtrip

#print axioms Qed.App.ssrStep_equiv_ssrRenderNativeBytes

#print axioms Qed.snapshotChildrenM_spec
#print axioms Qed.SubtreeInRange_to_SubtreeInSet
#print axioms Qed.SubtreeInSet_mono
#print axioms Qed.SubtreeInSet_frame
#print axioms Qed.InPlaceChildPatchSpec_setText
#print axioms Qed.keyed_step_insertBefore_create
#print axioms Qed.positional_step_reuse_tail
#print axioms Qed.positional_removeTail_spec
#print axioms Qed.applyKeyedStepsM_reconcile_spec
#print axioms Qed.applyKeyedStepsM_with_removeTail_spec
#print axioms Qed.hydrateTextSlotM_empty_spec
#print axioms Qed.hydrateTextSlotM_split_spec
#print axioms Qed.hydrateTextSlotM_head_spec
#print axioms Qed.hydrateDomM_spec
#print axioms Qed.hydrateDomKidsM_spec

#print axioms Js.Proofs.collectNonArr_mono
#print axioms Js.Proofs.collectNonArrAlts_mono
#print axioms Js.Proofs.collectNonArr_sound
#print axioms Js.Proofs.collectProjSrc_subset_collectNonArr
#print axioms Js.Proofs.hasDecOf_sound
#print axioms Js.Proofs.projRefTransfer_cowHeap_equiv
#print axioms Js.Proofs.lowerBody_equiv
#print axioms Js.Proofs.v_inj
#print axioms Js.Proofs.jp_inj
#print axioms Js.Proofs.v_ne_jp
#print axioms Js.Proofs.genGlobalName_inj
#print axioms Js.Proofs.genGlobalName_disjoint_all
#print axioms Js.Proofs.inlineJpSlot_inj
#print axioms Js.Proofs.ctxJs_fallback_startsWith_dollar
#print axioms Js.Proofs.mangle_chars_safe
#print axioms Js.Proofs.assignProgramNames_invariant
#print axioms Js.Proofs.ident_ne_jsKeyword
#print axioms Js.Proofs.jsStr_safe
#print axioms Js.Proofs.reach_closed
#print axioms Js.Proofs.reach_verifyNoServerLeak_sound
#print axioms Js.Proofs.noTailCont_of_hasJpSelfTail_false
#print axioms Js.Proofs.lowerDecl_equiv
#print axioms Js.Proofs.projTransfer_prefix_equiv

#print axioms Qed.Html.canonicalList_eq_map
#print axioms Qed.hasTag_canonical
#print axioms Qed.canonical_congr_pred
#print axioms Counter.app_view_eq
#print axioms Todo.app_view_eq
#print axioms Bookshelf.app_view_eq
#print axioms Qed.CleanDomSubtree_equiv
#print axioms Qed.applyPositionalStepsM_spec
#print axioms Qed.applyToDomM_spec
#print axioms Qed.patchHtmlSubtreeM_spec
#print axioms Qed.applyDynAttrsM_spec
#print axioms Qed.buildViewM_eq_buildDomM
#print axioms Qed.buildViewM_vstate_spec
#print axioms Qed.patchViewM_spec
#print axioms Qed.patchViewKidsM_spec
#print axioms Qed.alignRows_spec
#print axioms Qed.diffRowSigs_sound
#print axioms Qed.seedRowsM_spec
#print axioms Qed.renderSig_resolved_spec
#print axioms Qed.registerHandlerSpec_sound
#print axioms Qed.localMountSpec_init_vs_rerender
#print axioms Qed.gcLocalsSpec_frame
#print axioms Qed.snapshot_restore_locals_roundtrip
#print axioms Qed.drainPendingQueue_fifo_spec
#print axioms Qed.hydrateViewM_eq_hydrateDomM
#print axioms Qed.hydrateViewM_spec
#print axioms Qed.App.ssr_hydrate_patch_equiv
#print axioms Qed.sanitizeCssAtom_no_comment
#print axioms Qed.sanitizeCssSelector_no_comment
#print axioms Qed.sanitizeInlineCssAtom_no_comment
#print axioms Qed.renderStyleSheet_no_lt
#print axioms Qed.renderStyleSheet_no_closeSeq
#print axioms Qed.Theme.render_no_lt
#print axioms Qed.Theme.render_no_closeSeq
#print axioms Qed.Keyframes.rule_no_lt
#print axioms Qed.Keyframes.rule_no_closeSeq
#print axioms Qed.inlineStyleStr_no_lt
#print axioms Qed.inlineStyleStr_no_quote
#print axioms Qed.inlineStyleStr_no_closeSeq
#print axioms Qed.Attr.valid_inlineStyle
#print axioms Qed.Color.contrastX100_symm
#print axioms Qed.Color.contrastX100_self
#print axioms Qed.wcagAAA_implies_wcagAA
#print axioms Qed.wcagAA_implies_wcagAALarge
#print axioms Qed.roleLacks_canonical
#print axioms Qed.tagLacks_canonical
#print axioms Qed.roleHasAll_canonical
#print axioms Qed.tagHas_canonical
#print axioms Qed.noConflictingStyles_canonical
#print axioms Qed.App.guardRehydrate_sound
#print axioms Qed.App.guardRehydrate_complete
#print axioms Qed.ElemStateEquiv.dispatchInput
#print axioms Qed.View.DomClean_forEach

-- Client-Server RPC Preconditions, Postconditions (`Ensured`), & Fullstack Endpoint Closure
#print axioms Qed.Proto.encode_ensured
#print axioms Qed.ssr_rpc_endpoint_routed
#print axioms Qed.ssr_rpc_closure_complete
#print axioms Qed.Server.concurrent_schedule_ensures
#print axioms CloudBooks.Catalog.findAt_ensures
#print axioms CloudBooks.Catalog.order_ensures
#print axioms CloudBooks.Catalog.addBook_ensures
#print axioms CloudBooks.Storefront.orderedMatchesSlot
#print axioms CloudBooks.Main.rpc_endpoints_valid
#print axioms CloudBooks.Main.ssr_rpc_closure_complete
#print axioms Qed.rpcQueryKey_injective
#print axioms Qed.Cached.all_put
#print axioms Qed.Cached.all_lookup_state
#print axioms Qed.Query.boot_preserves_inv
#print axioms Qed.Query.wrap_preserves_inv

-- Verified Multiplexed & 3rd-Party WebSockets (Framing, Reconnect, Transactional Emit, Subscriptions & Closure)
#print axioms Qed.Reconnect.nextDelayMs_off
#print axioms Qed.Reconnect.nextDelayMs_exhausted_fixed
#print axioms Qed.Reconnect.nextDelayMs_exhausted_backoff
#print axioms Qed.Reconnect.nextDelayMs_backoff_le_max
#print axioms Qed.WsMuxFrame.decode_encode_unsub
#print axioms Qed.WsMuxFrame.decode_encode_send
#print axioms Qed.WsMuxFrame.decode_encode_joinOk
#print axioms Qed.WsMuxFrame.decode_encode_event
#print axioms Qed.wsTopicKey_injective
#print axioms Qed.Subscription.boot_preserves_inv
#print axioms Qed.Subscription.wrap_preserves_inv
#print axioms Qed.Subscription.wrap_noop_when_keys_unchanged
#print axioms Qed.fullstack_ws_closure_sound
#print axioms Qed.Server.external_ws_url_preserves_origin
#print axioms Qed.Server.srvFinishEmit_err_no_emits
#print axioms Qed.Server.srvAtomicCommitEmit_err_no_emits
#print axioms LiveRoom.Hub.inv_init
#print axioms LiveRoom.Hub.announce_inv
#print axioms LiveRoom.Hub.announce_ensures
#print axioms LiveRoom.Hub.room_onJoin_inv
#print axioms LiveRoom.Hub.room_onSend_inv
#print axioms LiveRoom.Hub.room_onLeave_inv
#print axioms LiveRoom.Hub.concurrent_linearizable
#print axioms LiveRoom.LiveApp.allMsgsValidRoom
#print axioms LiveRoom.LiveApp.app_view_eq
#print axioms LiveRoom.App.ws_endpoints_valid

-- Client-Side Prediction & Transactional Rollback (`SpecEngine`, `App.withSpeculative`)
#print axioms Qed.Demo.Signup.instLawfulBEq
#print axioms Qed.SpecEngine.replay_preserves_inv
#print axioms Qed.SpecEngine.drainConfirmed_preserves_inv
#print axioms Qed.SpecEngine.step_preserves_inv
#print axioms Qed.SpecEngine.step_preserves_coherent
#print axioms Qed.SpecEngine.step_preserves_wellFormedIds
#print axioms Qed.SpecEngine.resolve_hit_preserves_visible
#print axioms Qed.SpecEngine.resolve_hit_sound
#print axioms Qed.SpecEngine.resolve_rollback_reverts_single
#print axioms Qed.SpecEngine.resolve_unknown_noop
#print axioms Qed.SpecEngine.replacePending_split
#print axioms Qed.SpecEngine.resolve_general_linearizable
#print axioms Qed.SpecEngine.step_resolve_clears_when_last
#print axioms Qed.SpecEngine.resolve_all_drains_log
#print axioms Qed.SpecEngine.dispatch_never_fires_specMsg_cmd
#print axioms Qed.Internal.App.withSpeculative_init_inv
#print axioms Qed.Internal.App.withSpeculative_step_inv
#print axioms Qed.Internal.App.withSpeculative_init_coherent
#print axioms Qed.Internal.App.withSpeculative_step_coherent
#print axioms Qed.Internal.App.withSpeculative_init_wellFormedIds
#print axioms Qed.Internal.App.withSpeculative_step_wellFormedIds
#print axioms Qed.Internal.App.withSpeculative_rehydrate_sound
#print axioms Qed.Internal.App.withSpeculative_dehydrate_inv

-- Verified Collection Queries (`Qed.Collection`) & Extended `ForEach` Lifts
#print axioms Array.sumBy_push
#print axioms Array.sumBy_append
#print axioms Array.sumBy_mergeSort
#print axioms Array.sumBy_set
#print axioms Array.sumBy_eraseIdx
#print axioms Array.sumBy_filter_le
#print axioms Array.sumBy_pop_le
#print axioms Array.sumByInt_push
#print axioms Array.sumByInt_set
#print axioms Array.countWhere_push
#print axioms Array.countWhere_le_size
#print axioms Array.uniqueBy_push_iff
#print axioms Array.uniqueBy_filter
#print axioms Array.uniqueBy_mergeSort
#print axioms Array.isSortedBy_push_iff
#print axioms Array.isSortedBy_filter
#print axioms Array.isSortedBy_mergeSort_le
#print axioms Qed.ForEach.forall_append
#print axioms Qed.ForEach.forall_pop
#print axioms Qed.ForEach.forall_reverse
#print axioms Qed.ForEach.forall_extract
#print axioms Qed.ForEach.forall_eraseIdx
#print axioms Qed.ForEach.forall_set
#print axioms Qed.ForEach.forall_swap
#print axioms Qed.ForEach.forall_modify
