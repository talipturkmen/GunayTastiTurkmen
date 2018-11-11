open util/integer

 sig Time{
		date: one Int,
		hour: one Int,
		minutes: one Int
}
{ hour >=0 and hour<=5 and
	minutes >=0 and minutes<=5 and
	date>=1 and date <=2
 }

sig Location {
			coordX:one Int,
			coordY:one Int
				}
--{ coordX >= -90 and coordX <= 90 and coordY >= -180 and coordY <= 180 }
{coordX >=-3 and coordX<= -3 and coordY >=-6 and coordY=6 }

abstract sig Data{
			user: one IndividualUser,
			receiveTime:one Time
}
{
	this in user.data
}

sig LocationData extends Data{
		location:one Location
}
sig ProfileData extends Data {
}

sig HealthData extends Data{
		heartBeat: one Int
}
{
	heartBeat>=0 and heartBeat<=20
}

sig ChronicDisease extends Data{
		drugs:set UsedDrugs
}

sig UsedDrugs{
	dosePerDay:one Int
}
 {dosePerDay >0}

sig IndividualUser{
	data:some Data,
	services: set Service,
	preConfirmedThirdParties: set ThirdParty,
	receivedRequests: set IndividualDataRequest,
	--participatedOrganizations:set RunningOrganization,
	--spectatedOrganizations: set RunningOrganization		
}

sig ThirdParty{
	requests: set Request,
	services: set Service,
--	organizations: set RunningOrganization,
	address: one Location
}

abstract sig Service{}
one sig AutomatedSOS extends Service{}
one sig Track4Run extends Service{}

abstract sig Request{
	--requestTime: one Time,
	requestedData: one Data,
	status: RequestStatus,
	response: lone Response,
	requestedBy: one ThirdParty
}
{
	this in requestedBy.requests
}


sig IndividualDataRequest extends Request{
	user: one IndividualUser
}
sig AnonymDataRequest  extends Request{
}
abstract sig RequestStatus{
}
one sig Received extends RequestStatus{}
one sig Rejected extends RequestStatus{}
one sig Approved extends RequestStatus{}

sig Response{
	responseData: lone Data,
	status: one ResponseStatus,
	sentTo: one ThirdParty,
	--responseTime :one Time
}
{
	one r:Request|r.response=this
}
abstract sig ResponseStatus{
}
one sig RejectionSent extends ResponseStatus{}
one sig DataSent extends ResponseStatus{}

--<<<<<<<<<<<<<<<<<<<<<<<<<<<<<Data4Help Facts start>>>>>>>>>>>>>>>>>>>

--	If status of request is “Received” no response should be created
fact requestStatusReceivedResponseRelation{
	all r:Request| r.status= Received => #(r.response)=0
}

fact requestStatusAppRejectedResponseRelation{
	all r:Request|( r.status= Approved or r.status=Rejected) => r.response in Response and #(r.response)=1
}

--rejected Requests' responses should be rejection sent and responseData should be empty
fact requestRejectedFacts{
	all req: Request,res:Response| req.response=res and req.status=Rejected => res.status=RejectionSent and #(res.responseData)=0 and res.sentTo=req.requestedBy

}
--approved Requests' responses should be DataSent and responseDataShould be equal to RequestedData 
fact requestApprovedFacts{
	all req: Request,res:Response| req.response=res and req.status=Approved => res.status=DataSent and res.responseData= req.requestedData and res.sentTo=req.requestedBy
}

--every request should have it's own response
fact differentRequestDifferentResponse{
	no disj r1,r2:Request| r1.response=r2.response 
}

--Every user's data should be specific
fact differentUserDifferentData{
	no disj u1,u2:IndividualUser| u1.data=u2.data 
}

--There should be bidirectional relation between IndividualDataRequest and user
fact allIndividualRequestsAreRelatedToUser{
	all r:IndividualDataRequest, u:IndividualUser| r.user=u iff r in u.receivedRequests
}

fact bidirectionalRelationBetweenDataAndUser{
	all d:Data,u:IndividualUser| d.user=u iff d in u.data
}

-- Requested data of IndividualDataRequest and User should be related
fact DataRelationBetweenUserAndIndReq{
		all r:IndividualDataRequest, u:IndividualUser| r.user=u iff r.requestedData.user=u
}

--Every usedDrugs should be related with at least one disease
fact checkUsedDrugs{
	all d: UsedDrugs| some c:ChronicDisease| d in c.drugs
}

--Every request should be peculiar to it's ThirdParty
fact differentRequestDifferentThirdParty{
	no disj t1,t2: ThirdParty|  #(t1.requests & t2.requests)>0
}

--all Individual request which are requested by preconfirmedThirdparty should be approved
fact IndReqOfPreConfirmedShouldBeApproved{
	all i:IndividualDataRequest |i.requestedBy in i.user.preConfirmedThirdParties=> i.status=Approved
}

--Each user should has only one ProfileData
fact eachUserHasOnlyOneProfileData{
	all u:IndividualUser| #(ProfileData & u.data)=1
}	
--<<<<<<<<<<<<<<<<<<<<<<<<<<<<<Data4Help Facts end>>>>>>>>>>>>>>>>>>>


--Each response should be peculiar to a request
assert assert_differentRequestDifferentResponse{
	no r1,r2:Request| r1.response=r2.response 
}

--
assert assert_requestRejectedFacts{ 
	all req: Request,res:Response| req.response=res and req.status=Rejected => res.status=RejectionSent and #(res.responseData)=0
}
assert assert_requestApprovedFacts{
	all req: Request,res:Response| req.response=res and req.status=Approved => res.status=DataSent and res.responseData= req.requestedData
}
assert assert_checkRequestAndResponsesThirdParty{
	all req:Request, res:Response| req.response=res=> req.requestedBy=res.sentTo
}
pred requestIndividualData[u:IndividualUser,d:Data,s:RequestStatus,r:Response,rb:ThirdParty,/*t:Time,*/ i:IndividualDataRequest]{
	i.user=u
	i.requestedData=d
	i.status=s
	i.response=r
	i.requestedBy=rb
--	i.requestTime=t
}
pred isThereAnonymDataRequest{
	some AnonymDataRequest
}
--run isThereAnonymDataRequest for 4 but 1 Received, 1 Approved,1 Rejected,2 IndividualUser
--check assert_checkRequestAndResponsesThirdParty
--check assert_requestRejectedFacts
--check assert_differentRequestDifferentResponse
--run isThereAnonymDataRequest
run requestIndividualData
