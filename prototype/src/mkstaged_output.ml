include Mkstaged_head
module Make = struct

  (* Empty
  *)
  let internEmpty over =
    ()
  let defineEmpty = internEmpty StringSet.empty
  
  (* Carrier
  *)
  let internCarrier over =
    ()
  let defineCarrier = internCarrier StringSet.empty
  
  (* Magma
    f0 = *
  *)
  let internMagma over (f0:('a->'a->'a) ref) =
    ()
  let defineMagma (f0:('a->'a->'a) ref) = internMagma StringSet.empty f0
  
  (* PointedCarrier
    f0 = e
  *)
  let internPointedCarrier over (f0:'a) =
    ()
  let definePointedCarrier (f0:'a) = internPointedCarrier StringSet.empty f0
  
  (* PointedMagma
    f0 = *
    f1 = e
  *)
  let internPointedMagma over (f0:('a->'a->'a) ref) (f1:'a) =
    let over = StringSet.add "Carrier" over in
    if not (StringSet.mem "Magma" over) then internMagma over f0;
    if not (StringSet.mem "PointedCarrier" over) then internPointedCarrier over f1;
    ()
  let definePointedMagma (f0:('a->'a->'a) ref) (f1:'a) = internPointedMagma StringSet.empty f0 f1
  
  (* LeftUnital
    f0 = *
    f1 = e
  *)
  let internLeftUnital over (f0:('a->'a->'a) ref) (f1:'a) =
    if not (StringSet.mem "PointedMagma" over) then internPointedMagma over f0 f1;
    let k = !f0 in
    f0 := (fun p1 p2 -> match p1, p2 with (* leftIdentity_*_e *) | v0, v1 when v0=f1 -> v1 (* Continuation *) | _ -> k p1 p2
    );
    ()
  let defineLeftUnital (f0:('a->'a->'a) ref) (f1:'a) = internLeftUnital StringSet.empty f0 f1
  
  (* RightUnital
    f0 = *
    f1 = e
  *)
  let internRightUnital over (f0:('a->'a->'a) ref) (f1:'a) =
    if not (StringSet.mem "PointedMagma" over) then internPointedMagma over f0 f1;
    let k = !f0 in
    f0 := (fun p1 p2 -> match p1, p2 with (* rightIdentity_*_e *) | v0, v1 when v1=f1 -> v0 (* Continuation *) | _ -> k p1 p2
    );
    ()
  let defineRightUnital (f0:('a->'a->'a) ref) (f1:'a) = internRightUnital StringSet.empty f0 f1
  
  (* Unital
    f0 = *
    f1 = e
  *)
  let internUnital over (f0:('a->'a->'a) ref) (f1:'a) =
    let over = StringSet.add "PointedMagma" over in
    if not (StringSet.mem "LeftUnital" over) then internLeftUnital over f0 f1;
    if not (StringSet.mem "RightUnital" over) then internRightUnital over f0 f1;
    ()
  let defineUnital (f0:('a->'a->'a) ref) (f1:'a) = internUnital StringSet.empty f0 f1
  
  (* Semigroup
    f0 = *
  *)
  let internSemigroup over (f0:('a->'a->'a) ref) =
    if not (StringSet.mem "Magma" over) then internMagma over f0;
    ()
  let defineSemigroup (f0:('a->'a->'a) ref) = internSemigroup StringSet.empty f0
  
  (* Monoid
    f0 = *
    f1 = e
  *)
  let internMonoid over (f0:('a->'a->'a) ref) (f1:'a) =
    let over = StringSet.add "Magma" over in
    if not (StringSet.mem "Unital" over) then internUnital over f0 f1;
    if not (StringSet.mem "Semigroup" over) then internSemigroup over f0;
    ()
  let defineMonoid (f0:('a->'a->'a) ref) (f1:'a) = internMonoid StringSet.empty f0 f1
  
  (* UnaryOperation
    f0 = prime
  *)
  let internUnaryOperation over (f0:('a->'a) ref) =
    ()
  let defineUnaryOperation (f0:('a->'a) ref) = internUnaryOperation StringSet.empty f0
  
  (* PointedUnarySystem
    f0 = e
    f1 = prime
  *)
  let internPointedUnarySystem over (f0:'a) (f1:('a->'a) ref) =
    let over = StringSet.add "Carrier" over in
    if not (StringSet.mem "UnaryOperation" over) then internUnaryOperation over f1;
    if not (StringSet.mem "PointedCarrier" over) then internPointedCarrier over f0;
    ()
  let definePointedUnarySystem (f0:'a) (f1:('a->'a) ref) = internPointedUnarySystem StringSet.empty f0 f1
  
  (* InvolutivePointedMagmaSig
    f0 = *
    f1 = e
    f2 = prime
  *)
  let internInvolutivePointedMagmaSig over (f0:('a->'a->'a) ref) (f1:'a) (f2:('a->'a) ref) =
    let over = StringSet.add "Carrier" over in
    if not (StringSet.mem "PointedUnarySystem" over) then internPointedUnarySystem over f1 f2;
    if not (StringSet.mem "Magma" over) then internMagma over f0;
    ()
  let defineInvolutivePointedMagmaSig (f0:('a->'a->'a) ref) (f1:'a) (f2:('a->'a) ref) =
    internInvolutivePointedMagmaSig StringSet.empty f0 f1 f2
  
  (* InverseSig
    f0 = *
    f1 = e
    f2 = inv
  *)
  let internInverseSig over (f0:('a->'a->'a) ref) (f1:'a) (f2:('a->'a) ref) =
    if not (StringSet.mem "InvolutivePointedMagmaSig" over) then internInvolutivePointedMagmaSig over f0 f1 f2;
    ()
  let defineInverseSig (f0:('a->'a->'a) ref) (f1:'a) (f2:('a->'a) ref) = internInverseSig StringSet.empty f0 f1 f2
  
  (* LeftInverse
    f0 = *
    f1 = e
    f2 = inv
  *)
  let internLeftInverse over (f0:('a->'a->'a) ref) (f1:'a) (f2:('a->'a) ref) =
    if not (StringSet.mem "InverseSig" over) then internInverseSig over f0 f1 f2;
    let k = !f0 in
    f0 := (fun p1 p2 ->
      match p1, p2 with
      (* leftInverse_inv_*_e *)
      | v0, (PartialUnary (op0,v1)) when v1=v0 && op0==f2 -> f1
      (* Continuation *)
      | _ -> k p1 p2
    );
    ()
  let defineLeftInverse (f0:('a->'a->'a) ref) (f1:'a) (f2:('a->'a) ref) = internLeftInverse StringSet.empty f0 f1 f2
  
  (* RightInverse
    f0 = *
    f1 = e
    f2 = inv
  *)
  let internRightInverse over (f0:('a->'a->'a) ref) (f1:'a) (f2:('a->'a) ref) =
    if not (StringSet.mem "InverseSig" over) then internInverseSig over f0 f1 f2;
    let k = !f0 in
    f0 := (fun p1 p2 ->
      match p1, p2 with
      (* rightInverse_inv_*_e *)
      | (PartialUnary (op0,v0)), v1 when v1=v0 && op0==f2 -> f1
      (* Continuation *)
      | _ -> k p1 p2
    );
    ()
  let defineRightInverse (f0:('a->'a->'a) ref) (f1:'a) (f2:('a->'a) ref) = internRightInverse StringSet.empty f0 f1 f2
  
  (* Inverse
    f0 = *
    f1 = e
    f2 = inv
  *)
  let internInverse over (f0:('a->'a->'a) ref) (f1:'a) (f2:('a->'a) ref) =
    let over = StringSet.add "InverseSig" over in
    if not (StringSet.mem "LeftInverse" over) then internLeftInverse over f0 f1 f2;
    if not (StringSet.mem "RightInverse" over) then internRightInverse over f0 f1 f2;
    ()
  let defineInverse (f0:('a->'a->'a) ref) (f1:'a) (f2:('a->'a) ref) = internInverse StringSet.empty f0 f1 f2
  
  (* Group
    f0 = *
    f1 = e
    f2 = inv
  *)
  let internGroup over (f0:('a->'a->'a) ref) (f1:'a) (f2:('a->'a) ref) =
    let over = StringSet.add "InverseSig" over in
    if not (StringSet.mem "Monoid" over) then internMonoid over f0 f1;
    if not (StringSet.mem "Inverse" over) then internInverse over f0 f1 f2;
    ()
  let defineGroup (f0:('a->'a->'a) ref) (f1:'a) (f2:('a->'a) ref) = internGroup StringSet.empty f0 f1 f2
  
  (* AdditiveGroup
    f0 = +
    f1 = -
    f2 = 0
  *)
  let internAdditiveGroup over (f0:('a->'a->'a) ref) (f1:('a->'a) ref) (f2:'a) =
    if not (StringSet.mem "Group" over) then internGroup over f0 f2 f1;
    ()
  let defineAdditiveGroup (f0:('a->'a->'a) ref) (f1:('a->'a) ref) (f2:'a) = internAdditiveGroup StringSet.empty f0 f1 f2
  
  (* CommutativeMagma
    f0 = *
  *)
  let internCommutativeMagma over (f0:('a->'a->'a) ref) =
    if not (StringSet.mem "Magma" over) then internMagma over f0;
    ()
  let defineCommutativeMagma (f0:('a->'a->'a) ref) = internCommutativeMagma StringSet.empty f0
  
  (* CommutativeAdditiveMagma
    f0 = +
  *)
  let internCommutativeAdditiveMagma over (f0:('a->'a->'a) ref) =
    if not (StringSet.mem "CommutativeMagma" over) then internCommutativeMagma over f0;
    ()
  let defineCommutativeAdditiveMagma (f0:('a->'a->'a) ref) = internCommutativeAdditiveMagma StringSet.empty f0
  
  (* AbelianAdditiveGroup
    f0 = +
    f1 = -
    f2 = 0
  *)
  let internAbelianAdditiveGroup over (f0:('a->'a->'a) ref) (f1:('a->'a) ref) (f2:'a) =
    let over = StringSet.add "AdditiveMagma" over in
    if not (StringSet.mem "AdditiveGroup" over) then internAdditiveGroup over f0 f1 f2;
    if not (StringSet.mem "CommutativeAdditiveMagma" over) then internCommutativeAdditiveMagma over f0;
    ()
  let defineAbelianAdditiveGroup (f0:('a->'a->'a) ref) (f1:('a->'a) ref) (f2:'a) =
    internAbelianAdditiveGroup StringSet.empty f0 f1 f2
  
  (* AdditiveMagma
    f0 = +
  *)
  let internAdditiveMagma over (f0:('a->'a->'a) ref) =
    if not (StringSet.mem "Magma" over) then internMagma over f0;
    ()
  let defineAdditiveMagma (f0:('a->'a->'a) ref) = internAdditiveMagma StringSet.empty f0
  
  (* RingoidSig
    f0 = *
    f1 = +
  *)
  let internRingoidSig over (f0:('a->'a->'a) ref) (f1:('a->'a->'a) ref) =
    let over = StringSet.add "Carrier" over in
    if not (StringSet.mem "Magma" over) then internMagma over f0;
    if not (StringSet.mem "AdditiveMagma" over) then internAdditiveMagma over f1;
    ()
  let defineRingoidSig (f0:('a->'a->'a) ref) (f1:('a->'a->'a) ref) = internRingoidSig StringSet.empty f0 f1
  
  (* LeftRingoid
    f0 = *
    f1 = +
  *)
  let internLeftRingoid over (f0:('a->'a->'a) ref) (f1:('a->'a->'a) ref) =
    if not (StringSet.mem "RingoidSig" over) then internRingoidSig over f0 f1;
    let k = !f1 in
    f1 := (fun p1 p2 ->
      match p1, p2 with
      (* leftDistributive_*_+ *)
      | (PartialBinary (op0,v0,v1)), (PartialBinary (op1,v2,v3)) when v2=v0 && op1==f0 && op0==f0 -> (!f0 v0 (!f1 v1 v3))
      (* Continuation *)
      | _ -> k p1 p2
    );
    ()
  let defineLeftRingoid (f0:('a->'a->'a) ref) (f1:('a->'a->'a) ref) = internLeftRingoid StringSet.empty f0 f1
  
  (* RightRingoid
    f0 = *
    f1 = +
  *)
  let internRightRingoid over (f0:('a->'a->'a) ref) (f1:('a->'a->'a) ref) =
    if not (StringSet.mem "RingoidSig" over) then internRingoidSig over f0 f1;
    let k = !f1 in
    f1 := (fun p1 p2 ->
      match p1, p2 with
      (* rightDistributive_*_+ *)
      | (PartialBinary (op0,v0,v1)), (PartialBinary (op1,v2,v3)) when v3=v1 && op1==f0 && op0==f0 -> (!f0 (!f1 v0 v2) v1)
      (* Continuation *)
      | _ -> k p1 p2
    );
    ()
  let defineRightRingoid (f0:('a->'a->'a) ref) (f1:('a->'a->'a) ref) = internRightRingoid StringSet.empty f0 f1
  
  (* Ringoid
    f0 = *
    f1 = +
  *)
  let internRingoid over (f0:('a->'a->'a) ref) (f1:('a->'a->'a) ref) =
    let over = StringSet.add "RingoidSig" over in
    if not (StringSet.mem "LeftRingoid" over) then internLeftRingoid over f0 f1;
    if not (StringSet.mem "RightRingoid" over) then internRightRingoid over f0 f1;
    ()
  let defineRingoid (f0:('a->'a->'a) ref) (f1:('a->'a->'a) ref) = internRingoid StringSet.empty f0 f1
  
  (* Rng
    f0 = *
    f1 = +
    f2 = -
    f3 = 0
  *)
  let internRng over (f0:('a->'a->'a) ref) (f1:('a->'a->'a) ref) (f2:('a->'a) ref) (f3:'a) =
    let over = StringSet.add "RingoidSig" over in
    if not (StringSet.mem "AbelianAdditiveGroup" over) then internAbelianAdditiveGroup over f1 f2 f3;
    if not (StringSet.mem "Semigroup" over) then internSemigroup over f0;
    if not (StringSet.mem "Ringoid" over) then internRingoid over f0 f1;
    ()
  let defineRng (f0:('a->'a->'a) ref) (f1:('a->'a->'a) ref) (f2:('a->'a) ref) (f3:'a) = internRng StringSet.empty f0 f1 f2 f3
  
  (* CommutativeSemigroup
    f0 = *
  *)
  let internCommutativeSemigroup over (f0:('a->'a->'a) ref) =
    let over = StringSet.add "Magma" over in
    if not (StringSet.mem "Semigroup" over) then internSemigroup over f0;
    if not (StringSet.mem "CommutativeMagma" over) then internCommutativeMagma over f0;
    ()
  let defineCommutativeSemigroup (f0:('a->'a->'a) ref) = internCommutativeSemigroup StringSet.empty f0
  
  (* CommutativeMonoid
    f0 = *
    f1 = e
  *)
  let internCommutativeMonoid over (f0:('a->'a->'a) ref) (f1:'a) =
    let over = StringSet.add "Semigroup" over in
    if not (StringSet.mem "Monoid" over) then internMonoid over f0 f1;
    if not (StringSet.mem "CommutativeSemigroup" over) then internCommutativeSemigroup over f0;
    ()
  let defineCommutativeMonoid (f0:('a->'a->'a) ref) (f1:'a) = internCommutativeMonoid StringSet.empty f0 f1
  
  (* AdditiveCommutativeMonoid
    f0 = +
    f1 = 0
  *)
  let internAdditiveCommutativeMonoid over (f0:('a->'a->'a) ref) (f1:'a) =
    if not (StringSet.mem "CommutativeMonoid" over) then internCommutativeMonoid over f0 f1;
    ()
  let defineAdditiveCommutativeMonoid (f0:('a->'a->'a) ref) (f1:'a) = internAdditiveCommutativeMonoid StringSet.empty f0 f1
  
  (* Monoid1
    f0 = *
    f1 = 1
  *)
  let internMonoid1 over (f0:('a->'a->'a) ref) (f1:'a) =
    if not (StringSet.mem "Monoid" over) then internMonoid over f0 f1;
    ()
  let defineMonoid1 (f0:('a->'a->'a) ref) (f1:'a) = internMonoid1 StringSet.empty f0 f1
  
  (* LeftZero
    f0 = *
    f1 = e
  *)
  let internLeftZero over (f0:('a->'a->'a) ref) (f1:'a) =
    if not (StringSet.mem "PointedMagma" over) then internPointedMagma over f0 f1;
    let k = !f0 in
    f0 := (fun p1 p2 -> match p1, p2 with (* leftZero_*_e *) | v0, v1 when v0=f1 -> f1 (* Continuation *) | _ -> k p1 p2
    );
    ()
  let defineLeftZero (f0:('a->'a->'a) ref) (f1:'a) = internLeftZero StringSet.empty f0 f1
  
  (* Left0
    f0 = *
    f1 = 0
  *)
  let internLeft0 over (f0:('a->'a->'a) ref) (f1:'a) =
    if not (StringSet.mem "LeftZero" over) then internLeftZero over f0 f1;
    ()
  let defineLeft0 (f0:('a->'a->'a) ref) (f1:'a) = internLeft0 StringSet.empty f0 f1
  
  (* Semiring
    f0 = *
    f1 = +
    f2 = 0
    f3 = 1
  *)
  let internSemiring over (f0:('a->'a->'a) ref) (f1:('a->'a->'a) ref) (f2:'a) (f3:'a) =
    let over = StringSet.add "Ringoid0Sig" over in
    if not (StringSet.mem "AdditiveCommutativeMonoid" over) then internAdditiveCommutativeMonoid over f1 f2;
    if not (StringSet.mem "Monoid1" over) then internMonoid1 over f0 f3;
    if not (StringSet.mem "Ringoid" over) then internRingoid over f0 f1;
    if not (StringSet.mem "Left0" over) then internLeft0 over f0 f2;
    ()
  let defineSemiring (f0:('a->'a->'a) ref) (f1:('a->'a->'a) ref) (f2:'a) (f3:'a) = internSemiring StringSet.empty f0 f1 f2 f3
  
  (* Ring
    f0 = *
    f1 = +
    f2 = -
    f3 = 0
    f4 = 1
  *)
  let internRing over (f0:('a->'a->'a) ref) (f1:('a->'a->'a) ref) (f2:('a->'a) ref) (f3:'a) (f4:'a) =
    let over = StringSet.add "SemiRng" over in
    if not (StringSet.mem "Rng" over) then internRng over f0 f1 f2 f3;
    if not (StringSet.mem "Semiring" over) then internSemiring over f0 f1 f3 f4;
    ()
  let defineRing (f0:('a->'a->'a) ref) (f1:('a->'a->'a) ref) (f2:('a->'a) ref) (f3:'a) (f4:'a) =
    internRing StringSet.empty f0 f1 f2 f3 f4
  
  (* CommutativeRing
    f0 = *
    f1 = +
    f2 = -
    f3 = 0
    f4 = 1
  *)
  let internCommutativeRing over (f0:('a->'a->'a) ref) (f1:('a->'a->'a) ref) (f2:('a->'a) ref) (f3:'a) (f4:'a) =
    let over = StringSet.add "Magma" over in
    if not (StringSet.mem "Ring" over) then internRing over f0 f1 f2 f3 f4;
    if not (StringSet.mem "CommutativeMagma" over) then internCommutativeMagma over f0;
    ()
  let defineCommutativeRing (f0:('a->'a->'a) ref) (f1:('a->'a->'a) ref) (f2:('a->'a) ref) (f3:'a) (f4:'a) =
    internCommutativeRing StringSet.empty f0 f1 f2 f3 f4
  
  
  end
  