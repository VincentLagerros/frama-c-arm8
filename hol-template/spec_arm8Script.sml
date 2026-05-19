Theory spec_arm8
Ancestors words arm8

(* ----------------- *)
(* Utility functions *)
(* ----------------- *)

Definition arm8_load_64_def:
  arm8_load_64 m a =
  (((m (a + 7w)) @@
  (((m (a + 6w)) @@
  (((m (a + 5w)) @@
  (((m (a + 4w)) @@
  (((m (a + 3w)) @@
   (((m (a + 2w)) @@
     ((m (a + 1w)) @@ (m (a + 0w))):bool[16]):bool[24])):bool[32])
    ):bool[40])):bool[48])):bool[56])):bool[64])
End

(* ------------------ *)
(* Program boundaries *)
(* ------------------ *)

Definition swap_init_addr_def:
 swap_init_addr : word64 = 0x718w
End

Definition swap_end_addr_def:
 swap_end_addr : word64 = 0x730w
End

(* -------------- *)
(* ARMv8 contract *)
(* -------------- *)

(* ==== Function swap ====*)
Definition arm8_swap_pre_def:
 arm8_swap_pre (pre_x0:word64) (pre_x1:word64) (pre_x0_deref:word64) (pre_x1_deref:word64) (s:arm8_state) : bool =
  ((131072w <=+ pre_x0) /\
  (pre_x0 <+ 4294967296w) /\
  ((word_mod pre_x0 8w) = 0w) /\
  (131072w <=+ pre_x1) /\
  (pre_x1 <+ 4294967296w) /\
  ((word_mod pre_x1 8w) = 0w) /\
  (pre_x1_deref = (arm8_load_64 s.MEM pre_x1)) /\
  (pre_x0_deref = (arm8_load_64 s.MEM pre_x0)) /\
  (pre_x1 = (s.REG 1w)) /\
  (pre_x0 = (s.REG 0w)))
End

Definition arm8_swap_post_def:
 arm8_swap_post (pre_x0:word64) (pre_x1:word64) (pre_x0_deref:word64) (pre_x1_deref:word64) (st:arm8_state) : bool =
  (((arm8_load_64 st.MEM pre_x0) = pre_x1_deref) /\
  ((arm8_load_64 st.MEM pre_x1) = pre_x0_deref))
End