Require GHC.Err.
Require GHC.Base.

(* We might put these elsewhere, but these are some types that we 
   can use for untying the knots in DataCon/Class/PatSyn *)

Parameter DataConId : Type.
Parameter ClassId   : Type.
Parameter PatSynId  : Type.

Parameter Default_DataConId : GHC.Err.Default DataConId.
Parameter Default_ClassId   : GHC.Err.Default ClassId.
Parameter Default_PatSynId  : GHC.Err.Default PatSynId.

Parameter Eq_PatSynId  : Base.Eq_ PatSynId.
Parameter Eq_ClassId   : Base.Eq_ ClassId.
Parameter Eq_DataConId : Base.Eq_ DataConId.

Parameter Ord_PatSynId  : Base.Ord PatSynId.
Parameter Ord_ClassId   : Base.Ord ClassId.
Parameter Ord_DataConId : Base.Ord DataConId.


(*
-- An 'IdInfo' gives /optional/ information about an 'Id'.  If
-- present it never lies, but it may not be present, in which case there
-- is always a conservative assumption which can be made.

-- Most of the 'IdInfo' gives information about the value, or definition, of
-- the 'Id', independent of its usage. Exceptions to this
-- are 'demandInfo', 'occInfo', 'oneShotInfo' and 'callArityInfo'.
--

data IdInfo
  = IdInfo {
        arityInfo       :: !ArityInfo,          -- ^ 'Id' arity
        ruleInfo        :: RuleInfo,            -- ^ Specialisations of the 'Id's function which exist
                                                -- See Note [Specialisations and RULES in IdInfo]
        unfoldingInfo   :: Unfolding,           -- ^ The 'Id's unfolding
        cafInfo         :: CafInfo,             -- ^ 'Id' CAF info
        oneShotInfo     :: OneShotInfo,         -- ^ Info about a lambda-bound variable, if the 'Id' is one
        inlinePragInfo  :: InlinePragma,        -- ^ Any inline pragma atached to the 'Id'
        occInfo         :: OccInfo,             -- ^ How the 'Id' occurs in the program

        strictnessInfo  :: StrictSig,      --  ^ A strictness signature

        demandInfo      :: Demand,       -- ^ ID demand information
        callArityInfo   :: !ArityInfo,   -- ^ How this is called.
                                         -- n <=> all calls have at least n arguments

        levityInfo      :: LevityInfo    -- ^ when applied, will this Id ever have a levity-polymorphic type?
    }

*)

Parameter IdInfo        : Type.
Parameter vanillaIdInfo : IdInfo.
Parameter noCafIdInfo   : IdInfo.

Instance Default_IdInfo : GHC.Err.Default IdInfo :=
  GHC.Err.Build_Default _ vanillaIdInfo.

(* -------------------- *)

Parameter RuleInfo : Type.
Parameter emptyRuleInfo : RuleInfo.
Parameter isEmptyRuleInfo : RuleInfo -> bool.

Instance Default_RuleInfo : GHC.Err.Default RuleInfo :=
  GHC.Err.Build_Default _ emptyRuleInfo.


(* -------------------- *)

(*
Parameter RecSelParent : Type.
Parameter Default_RecSelParent : GHC.Err.Default RecSelParent.

Parameter Eq___RecSelParent : GHC.Base.Eq_ RecSelParent.
*)
