import Qed
import Qed.Deploy
import Qed.Server.Native
import Qed.Proofs.DomArena
import Qed.Proofs.ViewPatch
import Qed.Proofs.KeyedReconcile
import Qed.Proofs.Hydration
import Js.Proofs
import QedTests.AxiomFixtures
import QedTests.DbChecks
import QedTests.AuthChecks
import Examples.Counter
import Examples.Todo
import Examples.Signup
import Examples.Chat
import Examples.Bookshelf
import Examples.CloudBooks
import Examples.LiveRoom

private def manifest : String := "
Counter: counterSafe app_view_eq
Todo.Row: rowSafe rowStyled
Todo: rowsSafe rowsStyled app_view_eq
Account: canSubmit_iff
Chat: streamSafe
Qed: diff_apply diffChildren_apply applyChildrenTR_toList renderNode_eq_renderNodeFast
  renderChildren_eq_renderChildrenFast escapeHtml_eq_escapeHtmlFast sanitizeKey_eq_sanitizeKeyFast
  disambiguateKeys_eq_fast parse_depth_le parse_render hydrate_coalesce containsCloseSeq_escapeRawText
  escapeRawText_eq_fast isVoidTag_eq_fast encodeSeg_safe escapeHtml_no_markup_or_quote sanitizeKey_safe
  renderAttr_blocks_inline_handler renderAttr_blocks_srcdoc renderAttr_blocks_unsafe_url
  safeScriptSrc_no_markup_or_quote disambiguateKeys_nodup disambiguateKeys_size
  disambiguateKeys_of_nodup buildDomM_spec specDom_applyPatch_diff w3cInsertBefore_step
  w3cReconcileKeyed_eq hydrateTextRun_equiv hydrateDomM_ownsChildren_element patchViewM_memo_hit
  patchViewM_dyn_spec forEach_disambiguated_keys_nodup prefixMatchLen_bound prefixMatchLen_sound
  suffixMatchLen_sound collectChangedMarksLoop_sound patchNodeSlotAt_nextId patchNodeSlotAt_text_root
  rpc_wire_roundtrip fullstack_ssr_rpc_equiv validatedKeyIndex_spec diff_keyed_reuses
  diff_positional_reuses decodeSeg_encodeSeg sanitizeKey_of_safe renderAttr_valid_attr
  renderAttr_valid_flag renderAttr_valid_on renderAttr_no_angle_brackets renderAttrs_no_angle_brackets
  sanitizeCssAtom_safe sanitizeCssSelector_safe snapshotChildrenM_spec SubtreeInRange_to_SubtreeInSet
  SubtreeInSet_mono SubtreeInSet_frame InPlaceChildPatchSpec_setText keyed_step_insertBefore_create
  positional_step_reuse_tail positional_removeTail_spec applyKeyedStepsM_reconcile_spec
  applyKeyedStepsM_with_removeTail_spec hydrateTextSlotM_empty_spec hydrateTextSlotM_split_spec
  hydrateTextSlotM_head_spec hydrateDomM_spec hydrateDomKidsM_spec hasTag_canonical canonical_congr_pred
  CleanDomSubtree_equiv applyPositionalStepsM_spec applyToDomM_spec patchHtmlSubtreeM_spec
  applyDynAttrsM_spec buildViewM_eq_buildDomM buildViewM_vstate_spec patchViewM_spec patchViewKidsM_spec
  buildKeyIndex_spec verifiedLisFlags_spec diffRowSigs_sound seedRowsM_spec renderSig_resolved_spec
  registerHandlerSpec_sound localMountSpec_init_vs_rerender gcLocalsSpec_frame
  snapshot_restore_locals_roundtrip drainPendingQueue_fifo_spec hydrateViewM_eq_hydrateDomM
  hydrateViewM_spec sanitizeCssAtom_no_comment sanitizeCssSelector_no_comment
  sanitizeInlineCssAtom_no_comment renderStyleSheet_no_lt renderStyleSheet_no_closeSeq
  inlineStyleStr_no_lt inlineStyleStr_no_quote inlineStyleStr_no_closeSeq wcagAAA_implies_wcagAA
  wcagAA_implies_wcagAALarge roleLacks_canonical tagLacks_canonical roleHasAll_canonical
  tagHas_canonical noConflictingStyles_canonical ssr_rpc_endpoint_routed ssr_rpc_closure_complete
  rpcQueryKey_injective wsTopicKey_injective safeCanonicalHref_no_markup_or_quote
  escapeHeadMetaValue_no_markup_or_quote renderHeadMeta_empty
Qed.View: render_showIf collectDyn_showIf renderSig_showIf DomClean_forEach
Qed.Route: round_trip
Qed.TypedRoute: round_trip
Qed.Demo.Signup: canSubmit_iff instLawfulBEq
Qed.Demo: fixture_codecs_sound fixtureContrastBtn_contrast fixtureProject_ensures fixtureProject_blindTo
Qed.Demo.FixtureCompFn: inactiveClean app_view_eq
Qed.Json: render_eq_renderFast
Qed.LawfulJson: parse_render_toJson
Qed.Dict: get_set get_remove size_set size_remove_le
Qed.Url: isSafe
Qed.Router: isSafeUrl_toURL fromURL_toURL canonical_reparse
Qed.ToHref: isSafeUrl_toHref
Qed.V: render_memo
Qed.App: ssr_rehydrate_equiv ssrStep_equiv_ssrRenderNativeBytes ssr_hydrate_patch_equiv
  guardRehydrate_sound guardRehydrate_complete
Js.Proofs: jsTag_lowerCtor fieldProj_lowerCtor rtApp_under_compose rtApp_exact_equiv rtApp_over_equiv
  lowerBody_jdecl_nonrec_shape jdecl_inline_early_return_equiv jdecl_inline_jump_equiv
  lowerBody_selfTail_shape tailContinue_staged_assign_sound directLoop_equiv trampoline_equiv
  memo_thunk_obs_equiv collectNonArr_mono collectNonArrAlts_mono collectNonArr_sound
  collectProjSrc_subset_collectNonArr hasDecOf_sound projRefTransfer_cowHeap_equiv lowerBody_equiv v_inj
  jp_inj v_ne_jp genGlobalName_inj genGlobalName_disjoint_all inlineJpSlot_inj
  ctxJs_fallback_startsWith_dollar mangle_chars_safe assignProgramNames_invariant ident_ne_jsKeyword
  jsStr_safe reach_closed reach_verifyNoServerLeak_sound noTailCont_of_hasJpSelfTail_false
  lowerDecl_equiv projTransfer_prefix_equiv
Js.Proofs.CowHeap: cowUset_obs_equiv cowPush_obs_equiv refMark_creates_snapshot SnapshotValid_cowUset
  SnapshotValid_cowPush SnapshotValid_refMark refMark_snapshot_sound
Qed.Proto: decodeFrameList_append cursor_strictly_advances skipUnknown_preserves_lookup_suffix
  skipUnknown_preserves_repeated_suffix decodeHex_encodeHex decode_encode encode_ensured
Qed.Server: header_no_crlf external_url_preserves_origin readOnly_preserves_state
  concurrent_schedule_preserves_inv safeIO_bind_preservesStepRel concurrent_schedule_ensures
  external_ws_url_preserves_origin srvFinishEmit_err_no_emits srvAtomicCommitEmit_err_no_emits
Qed.Server.Net: base64UrlEncode_safe isBlockedIpBytes_loopback_v4 isBlockedIpBytes_metadata_v4
  isBlockedIpBytes_rfc1918_10 isBlockedIpBytes_testnet_v4 isBlockedIpBytes_benchmark_v4
  isBlockedIpBytes_loopback_v6 isBlockedIpBytes_v4mapped_metadata isBlockedIpBytes_nat64_metadata
  isBlockedIpBytes_nat64_local_v6 isBlockedIpBytes_6to4_v6 isBlockedIpBytes_teredo_v6
  isBlockedIpBytes_badLen parseHttpUrl_no_fragment
Qed.Server.Http: parseRequestHead_rejects_nul parseOneHeaderLine_rejects_bad_name
  parseRequestHead_http11_has_host parseRequestHead_contentLen_le safeContentType_no_crlf
  isContentHashedAsset_hashed isContentHashedAsset_plain classifyStaticPath_rejects_dotdot sha1_size
  base64Encode_rfc6455_accept decodeWsFrame_rejects_unmasked decodeWsFrame_rejects_rsv
CloudBooks.Catalog: inv_init list_readOnly findAt_readOnly cover_inv order_inv order_twoInv0
  order_mutInv0 addBook_inv addBook_twoInv0 addBook_mutInv0 concurrent_linearizable findAt_ensures
  order_ensures addBook_ensures
Qed.Cached: put_stale_preserves_state put_matching_updates_state put_non_ok_preserves_seen lookup_put_ok
  lookup_put_ok_sound put_seen_length_le all_put all_lookup_state
Qed.Query: wrap_preserves_inv wrap_noop_when_keys_unchanged boot_preserves_inv
Qed.Html: validIn_everyElementSafe valid_everyElementSafe canonicalList_eq_map
Qed.Item: render_no_lt renderList_no_lt render_no_closeSeq renderList_no_closeSeq
Qed.Style: rule_no_lt
Qed.LocalDef: valid_viewForProps dedupe_mem dedupe_ids_nodup decode_toJson_eq of_view_roundtrip
  ofProps_view_roundtrip
Bookshelf: app_view_eq
Qed.Theme: render_no_lt render_no_closeSeq
Qed.Keyframes: rule_no_lt rule_no_closeSeq
Qed.Attr: valid_inlineStyle
Qed.Color: contrastX100_symm contrastX100_self
Qed.ElemStateEquiv: dispatchInput
CloudBooks.Storefront: orderedMatchesSlot
CloudBooks.Main: rpc_endpoints_valid ssr_rpc_closure_complete
Qed.Reconnect: nextDelayMs_off nextDelayMs_exhausted_fixed nextDelayMs_exhausted_backoff
  nextDelayMs_backoff_le_max
Qed.WsMuxFrame: decode_encode_unsub decode_encode_send decode_encode_joinOk decode_encode_event
Qed.Subscription: boot_preserves_inv wrap_preserves_inv wrap_noop_when_keys_unchanged
LiveRoom.Hub: inv_init announce_inv announce_ensures room_onJoin_inv room_onSend_inv room_onLeave_inv
  secretFeed_project_ensures secretFeed_project_blindTo secretFeed_project_channel_ensures
  concurrent_linearizable
LiveRoom.LiveApp: allMsgsValidRoom app_view_eq
LiveRoom.App: ws_endpoints_valid
Qed.SpecEngine: replay_preserves_inv drainConfirmed_preserves_inv step_preserves_inv
  step_preserves_coherent step_preserves_wellFormedIds resolve_hit_preserves_visible resolve_hit_sound
  resolve_rollback_reverts_single resolve_unknown_noop replacePending_split resolve_general_linearizable
  step_resolve_clears_when_last resolve_all_drains_log dispatch_never_fires_specMsg_cmd
Qed.Internal.App: withSpeculative_init_inv withSpeculative_step_inv withSpeculative_init_coherent
  withSpeculative_step_coherent withSpeculative_init_wellFormedIds withSpeculative_step_wellFormedIds
  withSpeculative_rehydrate_sound withSpeculative_dehydrate_inv
Array: sumBy_push sumBy_append sumBy_mergeSort sumBy_set sumBy_eraseIdx sumBy_filter_le sumBy_pop_le
  sumByInt_push sumByInt_set countWhere_push countWhere_le_size uniqueBy_push_iff uniqueBy_filter
  uniqueBy_mergeSort isSortedBy_push_iff isSortedBy_filter isSortedBy_mergeSort_le
Qed.ForEach: forall_append forall_pop forall_reverse forall_extract forall_eraseIdx forall_set
  forall_swap forall_modify
Qed.Server.Db: isSafeSqlIdent_no_inject evalSelect_satisfies_policy evalInsert_preserves_inv
  evalUpdate_preserves_inv_and_trans evalDelete_preserves_inv_and_policy diffTableSchema_self_empty
  verifyMigrationSafe_nullable_addColumn aeadBase64Len_mono
Qed.Server.Db.SqlExpr: compile_sameShape
Qed.Server.Db.SqlQuery: compile_sameShape compile_no_semicolon
Qed.Server.Db.PgWire: encodeMsg_size
DbChecks.VaultDb.notes: rowInvBool_sound
DbChecks.VaultDb.books: rowInvBool_sound
DbChecks.VaultApi: getNote_ensures createNote_ensures editNote_ensures publishNote_ensures
  orderBook_ensures
DbChecks.ShopApi: createAuthorAndItem_inv createAuthorAndItem_ensures createPairDotSyntax_ensures
Qed.Server.SetCookie: render_no_crlf
Qed.Auth: parseJwtAlg_rejects_none parseJwtAlg_rejects_hs256 validateJwtClaims_rejects_expired
  validateJwtClaims_rejects_wrong_issuer validateJwtClaims_rejects_wrong_audience
  validateJwtClaims_rejects_empty_sub isSafeReturnTo_rejects_protocol_relative
  isSafeReturnTo_rejects_javascript sanitizeReturnTo_safe
Qed.Deploy: validate_rejects_bad_version validate_rejects_unsafe_auth_callback validate_default_ok
Qed.Base64: decode_encode encode_length encodeUrl_length
Qed.Mapping: decode_encode
Qed.Codec: run_refine_text run_refine_textarea
Qed: toString_field fromUTF8?_toUTF8
DbChecks.EncVaultDb.entries: rowInvBool_sound
DbChecks.EncVaultApi: save_ensures edit_ensures get_ensures
DbChecks.Base64BoundsMap: encode_ok decode_ok roundtrip decode_encode
DbChecks.DollarsToCentsMap: encode_ok decode_ok roundtrip decode_encode
DbChecks.NoteCipherMap: encode_ok decode_ok roundtrip decode_encode
DbChecks.FieldRenderCheck: app_view_eq
AuthChecks.AuthApi: adminAction_mutInv0
"

open Lean in
#eval show CoreM Unit from do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← getEnv
  let mut pfx : Name := .anonymous
  let mut seen : NameSet := {}
  for raw in manifest.splitOn "\n" do
    let t := raw.trimAscii.toString
    if t.isEmpty || t.startsWith "--" then continue
    let rest ← match t.splitOn ":" with
      | [p, r] =>
          pfx := (p.trimAscii.toString.splitOn ".").foldl Name.mkStr .anonymous
          pure r
      | [r] => pure r
      | _ => throwError "malformed axioms manifest line: {t}"
    for leaf in (rest.splitOn " ").filter (!·.isEmpty) do
      let n := Name.mkStr pfx leaf
      unless env.contains n do
        throwError "missing theorem in axioms manifest: {n}"
      if seen.contains n then
        throwError "duplicate theorem in axioms manifest: {n}"
      seen := seen.insert n
      let axs ← collectAxioms n
      let bad := axs.filter (!allowed.contains ·)
      unless bad.isEmpty do
        throwError "unexpected axiom(s) in {n}: {bad.toList}"
  unless seen.size == 421 do
    throwError "expected 421 theorems in axioms manifest, checked {seen.size}"
  IO.println s!"✓ {seen.size} theorems checked: 0 unexpected axioms"
