Require Import
        Coq.Vectors.Vector
        Coq.Strings.Ascii
        Coq.Bool.Bool
        Coq.Lists.List
        Bedrock.Word
        Bedrock.Memory
        Fiat.Computation.ListComputations.

Require Import
        Fiat.QueryStructure.Automation.AutoDB
        Fiat.Examples.DnsServer.Packet.

Import Coq.Vectors.VectorDef.VectorNotations.

Local Open Scope vector.

(* The schema, packet structure, and spec are based on the following four RFCs:

RFC 1034: high-level DNS outline
RFC 1035: implementation details
RFC 2308: negative caching -- for more information on failures and SOA records
RFC 1536: common implementation errors and fixes -- for efficiency/security problems *)

(* What subdomain we're on in a question, e.g. new requests get stage None *)
(* when working on a referral, the stage is set to the match count b/t the *)
(* referral and question e.g. question = s.g.com, referral = for g.com, *)
(* stage = match count = 2 (excluding root) *)

(* String definitions *)
Definition sREQUESTS := "Requests".
Definition sSTAGE := "Stage".
Definition sID := "ID".
Definition sIP := "IP".
Definition sRESULT := "Result".
Definition sDOMAIN := "Domain".

Definition sCACHE := "Cache".
Definition sSERVER := "Server".
Definition sPID := "Packet id".
Definition sFLAGS := "Packet flags".

Definition sHOST := "Source host".
Definition sEMAIL := "Contact email".
Definition sSERIAL := "Serial number".
Definition sREFRESH := "Refresh time".
Definition sRETRY := "Retry time".
Definition sEXPIRE := "Expire time".
Definition sMinTTL := "minTTL".
Definition sPACKET := "Packet".

Definition sREFERRALDOMAIN := "Referral domain".
Definition sRTYPE := "Referral domain type".
Definition sRCLASS := "Referral domain class".
Definition sRTTL := "Referral domain TTL".
Definition sSERVERDOMAIN := "Server domain".
Definition sSTYPE := "Server type".
Definition sSCLASS := "Server class".
Definition sSTTL := "Server TTL".
Definition sSIP := "Server IP".

Definition sQNAME := "Question name".
Definition sQTYPE := "Question type".
Definition sQCLASS := "Question class".
Definition sCACHETYPE := "Cache type".
Definition sCACHEDVALUE := "Cached value".

Definition sREQID := "Request ID".
Definition sREFERRALID := "Referral ID".
Definition sMATCHCOUNT := "# labels matched".
Definition sQUERYCOUNT := "# times queried".

Definition sORDER := "SLIST order". (* using referral IDs *)
Definition sSLIST := "SLIST".
Definition sSLIST_ORDERS := "SLIST orders".

Definition sTIME_LAST_CALCULATED := "Time the TTL was last calculated".
Local Open Scope Heading_scope.

(* Unique Request IDs *)
Definition ID : Type := word 16.

(* Heading for a pending request. This is a packet plus a *)
(* unique ID associated with the request and a timeout for *)
(* discarding stale requests. *)
Definition RequestHeading : Heading :=
  < sID :: ID,    (* unique, ascending *)
    sIP :: W,     (* IP address of the request source*)
    sTTL :: timeT > (* Timeout for request *)
    ++ packetHeading.

(* The heading of current resource records for known servers *)
(* (called the SLIST in RFC 1035); these records are augmented *)
(* with a query count field that is used to ensure fair distribution *)
(* of queries among a domain's nameservers. The desing decision here *)
(* is that when new servers are discovered, the resolver will do *)
(* the necessary address/name linking before recording them in this *)
(* list. *)
Definition SLISTHeading :=
  < sQUERYCOUNT :: W, (* number of times we've queried this server *)
    sTTL :: timeT, (* Domain of known server *)
    sDOMAIN :: DomainName, (* Domain of known server *)
    sIP :: W > (* Address of server. *).

(* The cache holds either answers (resource records returned by a *)
(* query) or failures (negative responses). *)
Definition CacheType :=
  BoundedString ["Answer"; "Failure"].

(* Stores an SOA (Start of Authority) record for cached failures, *)
(* according to RFC 2308. The SOA's TTL is used as the length of *)
(* time to assume a name failure. *)

Definition CachedValueTypes :=
  [ resourceRecord; SOA_Record ].

Definition CachedValue := SumType CachedValueTypes.

Definition rRecord2CachedValue (vrr : resourceRecord)
  : CachedValue := inj_SumType CachedValueTypes (ibound (indexb (Bound := ["Answer"; "Failure"]) ``"Answer")) vrr.

Definition Failure2CachedValue (vrr : SOA_Record)
  : CachedValue := inj_SumType CachedValueTypes (ibound (indexb (Bound := ["Answer"; "Failure"]) ``"Failure")) vrr.

(* Only cache specific resource records in response to a query. *)
Definition CachedQueryTypes :=
  BoundedString (OurRRecordTypes ++ ExtraRRecordTypes).

Definition CachedQueryTypes_inj (rr : CachedQueryTypes) : QType :=
  BoundedIndex_injR rr.

Coercion CachedQueryTypes_inj : CachedQueryTypes >-> QType.
Coercion rRecord2CachedValue : resourceRecord >-> CachedValue.
Coercion Failure2CachedValue : SOA_Record >-> CachedValue.

Definition CacheHeading :=
  < sTTL :: timeT, (* Lifetime of cached value *)
    sCACHETYPE :: CacheType, (* Type of cached value *)
    sDOMAIN:: DomainName, (* Domain of cached Query*)
    sQTYPE :: CachedQueryTypes,  (* Type of cached query *)
    sCACHEDVALUE :: CachedValue >. (* Cached data *)

Definition RecResolverSchema :=
  Query Structure Schema
        [ relation sREQUESTS has schema RequestHeading;

          relation sSLIST has schema SLISTHeading;

          relation sCACHE has schema CacheHeading ]
        enforcing [ ].

Definition requestTTL : timeT := natToWord _ 0.

(* Should probably restrict cache to have either an answer *)
(* or a failure for a domain and question type. *)

Open Scope Tuple_scope.

Definition DnsSpec : ADT _ :=
  Def ADT {
    rep := QueryStructure RecResolverSchema,

    Def Constructor "Init" : rep := empty,,

    Def Method3 "Process"
        (this : rep)
        (sourceIP : W)
        (curTime : timeT)
        (p : packet) : rep * packet * W :=
      If p!"QR" Then
         (* It's a new request! *)
         vs <- For (v in this!sCACHE) (* Search cache for an answer *)
              Where (p!"questions"!"qtype" = CachedQueryTypes_inj v!sQTYPE)
              Where (curTime <= v!sTTL) (* only alive cached values *)
              Return (v ! sCACHEDVALUE) ;
         If is_empty vs Then (* Need to launch a recursive query *)
                  (* Step 1: Generate a unique ID for the new request. *)
            (reqIDs <- For (req in this!sREQUESTS)
                       Where (curTime <= req!sTTL)
                       Return (req!sID);
             newID <- { newID | ~ List.In newID reqIDs};
             (* Find the best known servers to query *)
             bestServer <- MaxElement
                             (fun r r' : @Tuple SLISTHeading =>
                                IsPrefix r!sDOMAIN r'!sDOMAIN
                                /\ r!sQUERYCOUNT <= r'!sQUERYCOUNT)
                             (For (server in this!sSLIST)
                              Where (IsPrefix server!sDOMAIN p!"questions"!"qname")
                              Where (curTime <= server!sTTL)
                              Return server);
             Ifopt bestServer as bestServer Then (* Pick the first server*)
             `(this, b) <- Insert < sID :: newID,
                                    sIP :: sourceIP,
                                    sTTL :: requestTTL > ++ p into this!sREQUESTS;
             ret (this, (<"id" :: newID,
                             "QR" :: false,
                             "Opcode" :: ``"Query",
                             "AA" :: false,
                             "TC" :: false,
                             "RD" :: true,
                             "RA" :: false,
                             "RCode" :: ``"NoError",
                             "question" :: p!"questions",
                             "answers" :: [ ],
                             "authority" :: [ ],
                             "additional" :: [ ] >, bestServer!sIP))
             Else (* There are no known servers that can answer this request. *)
             ret (this, (buildempty false ``"ServFail" p, sourceIP)) (* This won't happen if the server has been properly initialized with the root servers. *)
            )
       Else                   (* Return cached answer *)
         (answers <- { answers | forall ans : resourceRecord, List.In ans answers <-> List.In (A := CachedValue) ans vs };
          If is_empty answers Then (* It must be a cached failure *)
             failures <- { failures | forall fail : SOA_Record, List.In (A := resourceRecord) fail failures <-> List.In (A := CachedValue) fail vs };
             ret (this, (add_additionals failures (buildempty false ``"NXDomain" p), sourceIP)) (* Add the SoA record to additional and return negative result*)
          Else
          ret (this, (add_answers answers (buildempty false ``"NoError" p), sourceIP)))
         (* Add the answers to the packet.  *)
      Else (* It's a response, so we need to associate the packet with *)
           (* an in-flight request. *)
      ret (this, (p, natToWord _ 0))
        }.


(* TODO the SOA is technically supposed to go in the Authority section
but the packet type doesn't include it *)



(* position in SLIST *)
Definition position := W.
(* e.g. ["192", "168", "1", "1"] *)
Definition IP := DomainName.

(* Type of the things that we (the server) can send to the wrapper, including *)
(* various error codes and responses. *)
Inductive ToOutside : Type :=
(* Errors *)
| InvalidQuestion : id -> ToOutside
| InvalidResponse : id -> ToOutside
| InvalidPacket : id -> packet -> ToOutside
| MissingSOA : id -> packet -> ToOutside
| InternalCacheError : id -> packet -> ToOutside
| NoReferralsLeft : id -> packet -> ToOutside
| InvalidId : id -> packet -> ToOutside
(* Responses *)
(* We were referred to the server with ip IP, and ask it the same question. *)
(* Request is pending *)
| ServerQuestion : id -> IP -> packet -> ToOutside
(* Request is finished *)
| ClientAnswer : id -> packet -> ToOutside
| ClientFailure : id -> packet -> SOA_RDATA -> ToOutside.

(* Type of things we store for a finished request. (Note no referrals) *)
Inductive ToStore : Type :=
| Answer : DomainName -> packet -> ToStore
| Failure : DomainName -> packet -> SOA_RDATA -> ToStore.

(* The section of a packet that a certain answer (DNSRRecord) is in, *)
(* used to tag the flattened rows from a packet. Needed because they're *)
(* all of type answer so there's no other way to distinguish them *)
Inductive PacketSection : Type :=
| PAnswer : PacketSection
| PAuthority : PacketSection
| PAdditional : PacketSection.


(* ------------------ Schema headings *)

(* The ideal schema would be domain and WrapperResponse, with some way *)
(* to query the types nested in WrapperResponse. Flattening it here has *)
(* the same effect. *)

(* One (Domain => WrapperResponse) mapping is flattened into several rows *)
(* that all have the same packet information, but store one answer *)
(* (DNSRRecord) each. *)

(* When removing a (Domain => ToStore): delete rows with the Domain in *)
(* all cache tables. *)

(* When inserting/updating a new (Domain => ToStore): after checking that *)
(* Domain doesn't exist in any of the cache tables (or just performing a *)
(* delete), flatten it and insert each row. *)

(* Invariants: (TODO) *)
(* - All rows for each domain should appear in exactly 1 of the cache *)
(*   relations (question, answer, or failure). We do not store multiple *)
(*   possibilities. *)
(* - All rows for each domain should have the same packet info. *)

(* Heading for cached referrals. Same as above but without the "live" *)
(* information (ids, match and query count) and with cache info (TTL and *)
(* time the TTL was last calculated) *)

Definition ReferralHeading :=
  (* R- = referral domain's, S- = server domain's *)
  < sREFERRALDOMAIN :: DomainName,
    sRTYPE :: RRecordType,
    sRCLASS :: RRecordClass,
    sRTTL :: W,
    (* inline RDATA and additional record *)
    sSERVERDOMAIN :: DomainName,
    sSTYPE :: RRecordType,
    sSCLASS :: RRecordClass,
    sSTTL :: W,
    sSIP :: DomainName,
    (* IP in RDATA of additional record *)
    sTIME_LAST_CALCULATED :: timeT
>.

(*  Stores a cached answer (DNSRRecord). Might have appeared in the *)
(*  answer, authority, or additional section of a packet. *)
(*  sDOMAIN and sNAME may differ in the case of CNAME, where *)
(*  sDOMAIN is an alias for sNAME. See RFC 1034, 6.2.7  *)

Definition AnswerHeading :=
  < sDOMAIN :: DomainName,
    sPACKET_SECTION :: PacketSection,
    sTIME_LAST_CALCULATED :: timeT>
    ++ resourceRecordHeading.

(* Stores an SOA (Start of Authority) record for cached failures,
according to RFC 2308. The SOA's TTL is used as the length of time to
assume a name failure *)

(* TODO the SOA is technically supposed to go in the Authority section
but the packet type doesn't include it *)

Definition FailureHeading :=
  < sDOMAIN :: DomainName,
    sTIME_LAST_CALCULATED :: timeT>
    ++ SOAHeading.

Definition ReferralRow := @Tuple ReferralHeading.
Definition SLIST_ReferralRow := @Tuple SLIST_ReferralHeading.
Definition AnswerRow := @Tuple AnswerHeading.
Definition FailureRow := @Tuple FailureHeading.
Definition RequestRow := @Tuple RequestHeading.

(* Type of things that a cache query can return.
Process gets ALL the rows that match; we don't do any filtering.
Process deals with re-hierarchizing, choosing the best result, etc. *)
Inductive CacheResult :=
| Nope : CacheResult
(* Nonempty lists *)
| Ref : list ReferralRow -> CacheResult
| Ans : list AnswerRow -> CacheResult
(* A failure stores exactly one result (the SOA) *)
| Fail : option FailureRow -> CacheResult.

(* Type used in the cache pointer table, which maps names that exist in the cache
somewhere to the table that they're in.
We need to cache referrals, but never in relation to a specific name, which is why
they're not in this type. (For a particular request with a name, it will always end in Answer or Failure) *)
Inductive CacheTable :=
| CAnswers
| CFailures.

(* Type for SLIST order. See RFC 1034, page 32 for a more detailed
description of the SLIST.

SLIST: a structure which describes the name servers and the
       zone which the resolver is currently trying to query.
       This structure keeps track of the resolver's current
       best guess about which name servers hold the desired
       information; it is updated when arriving information
       changes the guess.

Here, an SLIST is a list of current referrals we have, sorted by
descending match count (so the first one to be used should have the
highest match count). (TODO: should also incorporate query count) We
store the referrals in one table and their positions in another
table. Each request's SLIST is a list of (refId, position).

The SLIST is deleted after a request finishes (ends in an answer or
failure). Individual referrals may be cleared when their TTL runs
out. *)
Record refPosition := { refId : id; refPos : W }.

Definition DnsRecSchema :=
  Query Structure Schema
        [ relation sREQUESTS has
                   schema
                   RequestHeading;

            (* (* Described above *) *)
            (* (* caching optimization opportunity!!!! (ACTION ITEM) *) *)
            (* relation sSLIST_ORDERS has schema *)
            (*          < sREQID :: id, *)
            (*            sORDER :: list refPosition *)
            (*                   (* id instead + func *) *)
            (*          >; *)
            (*          (* reqid, refid, refpos *) *)
            relation sSLIST has
                     schema
                     SLIST_ReferralHeading;

            relation sCACHE_POINTERS has schema
            < sDOMAIN :: DomainName,
            sCACHETABLE :: CacheTable
            (* would like to have a variant type in the schema *)
            > ;
            relation sCACHE_ANSWERS has
                     schema
                     AnswerHeading;
            relation sCACHE_REFERRALS has
                     schema
                     ReferralHeading;
            relation sCACHE_FAILURES has
                     schema
                     FailureHeading
        ]
        enforcing [ ].
(* where (fun t t' => True) ] *)
(* TODO use an attribute constraint to encode that Stage <= length name *)
(* TODO other invariants are not encoded *)

(* Wrappers for building various tuples. *)
Open Scope Tuple_scope.
(*Definition Build_RequestState (pac : packet) (id' : id) (stage : Stage) :=
  < "id" :: id',
  sQNAME :: pac!"questions"!"qname",
  sSTAGE :: stage,
  sQTYPE :: pac!"questions"!"qtype",
  sQCLASS :: pac!"questions"!"qclass",
  sPID :: pac!"id",
  sFLAGS :: pac!"flags">%Tuple. *)

Definition Build_CachePointerRow
           (reqName : DomainName)
           (table : CacheTable) :=
  < sDOMAIN :: W, sCACHETABLE :: table >%Tuple.


Definition ToSLISTRow (refRow : ReferralRow)
           (reqId : W)
           (refId : W)
           (matchCount : W)
           (queryCount : W)
  : SLIST_ReferralRow :=
  < sREQID :: reqId, sREFERRALID :: refId,
  sMATCHCOUNT :: matchCount, sQUERYCOUNT :: queryCount >
                             ++ refRow.

Definition ToSLISTOrder (reqId : W)
           (order : list refPosition) :=
  < sREQID :: reqId, sORDER :: order >.

Definition toPacket_soa (soa : FailureRow) : SOA_RDATA :=
  prim_snd (prim_snd soa).

Definition toPacket_ans (ans : AnswerRow) : resourceRecord :=
  prim_snd (prim_snd (prim_snd ans)).

(* So long strings of Ascii Bool Bool... won't show up in Set Printing All *)
Definition Init := "Init".
Definition MakeId := "MakeId".
Definition AddRequest := "AddRequest".
Definition GetRequestStage := "GetRequestStage".
Definition UpdateRequestStage := "UpdateRequestStage".
Definition GetServerForLongestSuffix := "GetServerForLongestSuffix".
Definition InsertResultForDomain := "InsertResultForDomain".
Definition DeletePendingRequestInfo := "DeletePendingRequestInfo".
Definition DeleteCachedNameResult := "DeleteCachedNameResult".
Definition PacketToReferralRows :="PacketToReferralRows".
Definition InsertReferralRowsIntoCache := "InsertReferralRowsIntoCache".
Definition ReferralRowsToSLIST := "ReferralRowsToSLIST".
Definition GetFirstReferralAndUpdateSLIST := "GetFirstReferralAndUpdateSLIST".
Definition SortSLIST := "SortSLIST".
Definition UpdateCacheReferralsAndSLIST := "UpdateCacheReferralsAndSLIST".
Definition UpdateTTLs := "UpdateTTLs".
Definition Process := "Process".

Coercion

Definition default_refresh_time : W := natToWord _ 3600. (* seconds *)
Definition default_retry_time : W := natToWord _ 600.
Definition default_expire_time : W := natToWord _ 600.
(* may cause stack overflow / segfault; use hours instead? *)
Definition default_minimum_TTL : W := natToWord _ 3600.