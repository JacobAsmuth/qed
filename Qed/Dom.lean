namespace Qed.Dom

abbrev Node := UInt32

@[extern "qed_dom_create_element"]
opaque createElement (ns tag : String) : IO Node

@[extern "qed_dom_child_namespace"]
opaque childNamespace (node : Node) : IO String

def svgNs : String := "http://www.w3.org/2000/svg"

@[inline] def childNsOf (ns tag : String) : String :=
  if tag == "foreignObject" then ""
  else if ns == svgNs || (ns == "" && tag == "svg") then svgNs
  else ""

@[extern "qed_dom_create_text"]
opaque createText (content : String) : IO Node

@[extern "qed_dom_create_fragment"]
opaque createFragment : IO Node

@[extern "qed_dom_set_attribute"]
opaque setAttribute (node : Node) (key value : String) : IO Unit

@[extern "qed_dom_remove_attribute"]
opaque removeAttribute (node : Node) (key : String) : IO Unit

@[extern "qed_dom_retain_attributes"]
opaque retainAttributes (node : Node) (names : List String) : IO Unit

@[extern "qed_dom_get_attribute"]
opaque getAttribute (node : Node) (key : String) : IO String

@[extern "qed_dom_clear_handlers"]
opaque clearHandlers (node : Node) : IO Unit

@[extern "qed_dom_app_state"]
opaque appState : IO String

@[extern "qed_dom_set_value"]
opaque setValue (node : Node) (value : String) : IO Unit

@[extern "qed_dom_set_checked"]
opaque setChecked (node : Node) (on : Bool) : IO Unit

@[extern "qed_dom_today"]
opaque today : IO String

@[extern "qed_dom_fetch_stream"]
opaque fetchStream (url body : String) (chunkId doneId : UInt32) : IO Unit

@[extern "qed_dom_http_send"]
opaque httpSend (method url body : String) (id : UInt32) : IO Unit

@[extern "qed_dom_current_path"]
opaque currentPath : IO String

@[extern "qed_dom_push_path"]
opaque pushPath (path : String) : IO Unit

@[extern "qed_dom_append_child"]
opaque appendChild (parent child : Node) : IO Unit

@[extern "qed_dom_set_text"]
opaque setText (node : Node) (content : String) : IO Unit

@[extern "qed_dom_child_at"]
opaque childAt (parent : Node) (index : UInt32) : IO Node

@[extern "qed_dom_app_root"]
opaque appRoot : IO Node

@[extern "qed_dom_child_count"]
opaque childCount (parent : Node) : IO UInt32

@[extern "qed_dom_remove_child"]
opaque removeChild (parent : Node) (index : UInt32) : IO Unit

@[extern "qed_dom_replace_child"]
opaque replaceChild (parent : Node) (index : UInt32) (newChild : Node) : IO Unit

@[extern "qed_dom_insert_before"]
opaque insertBefore (parent : Node) (index : UInt32) (child : Node) : IO Unit

@[extern "qed_dom_mount_root"]
opaque mountRoot (node : Node) : IO Unit

@[extern "qed_dom_is_connected"]
opaque isConnected (node : Node) : IO Bool

@[extern "qed_dom_effect"]
opaque effect (kind a b c : String) : IO Unit

@[extern "qed_dom_effect_result"]
opaque effectResult (kind a b : String) (id : UInt32) : IO Unit

@[extern "qed_dom_port_send"]
opaque portSend (name payload : String) : IO Unit

@[extern "qed_dom_bind_signal"]
opaque bindSignal (node : Node) (name : String) : IO Unit

@[extern "qed_dom_bind_signal_attr"]
opaque bindSignalAttr (node : Node) (name attr : String) : IO Unit

end Qed.Dom
