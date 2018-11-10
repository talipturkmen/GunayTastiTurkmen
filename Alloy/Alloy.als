open util/integer

sig Date{}
sig Time{
		date: one Date,
		hour: one Int,
		minutes: one Int
}
{ hour >=0 and hour<=5 and
	minutes >=0 and minutes<=7
 }

sig Location {
				--latitude
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
}

sig ChronicDisease extends Data{
		drugs:set UsedDrugs
}

sig UsedDrugs{
	dosePerDay:one Int
}

sig IndividualUser{
	data:some Data,
	services: set Service,
	preConfirmedThirdParties: set ThirdParty,
	requests: set IndividualDataRequest,
	participatedOrganizations:set RunningOrganization,
	spectatedOrganizations: set RunningOrganization		
}

sig ThirdParty{
	requests: set Request,
	services: set Service,
	organizations: set RunningOrganization,
	address: one Location
}
abstract sig Service{}
one sig AutomatedSOS extends Service{}
one sig Track4Run extends Service{}

sig RunningOrganization{
	organizer: one ThirdParty,
	runners: some IndividualUser,
	spectators: set IndividualUser,
	path: one Path,
	time: one Time
}

sig Path{
	organization: RunningOrganization,
	startLocation: one Location,
	intermediaryLocation: one Location,
	endLocation: one Location
}
{
	no l: intermediaryLocation | startLocation=l or endLocation=l
}

abstract sig Request{
	requestTime: one Time,
	requestedData: one Data,
	status: RequestStatus,
	response: one Response,
}
{
	some t:ThirdParty | this in t.requests
}

sig IndividualDataRequest extends Request{
	user: some IndividualUser
}
sig AnonymDataRequest  extends Request{
}

sig Response{
	responseData: lone Data,
	status: one ResponseStatus,
	sentTo: one ThirdParty,
	responseTime :one Time
}
{
	one r:Request|r.response=this
}
abstract sig ResponseStatus{
}
one sig RejectionSent extends ResponseStatus{}
one sig DataSent extends ResponseStatus{}
abstract sig RequestStatus{
}

one sig Rejected extends RequestStatus{}
one sig Approved extends RequestStatus{}

fact requestRejectedFacts{
	all req: Request,res:Response| req.response=res and req.status=Rejected => res.status=RejectionSent and #(res.responseData)=0

}
fact requestRejectedFacts{
	all req: Request,res:Response| req.response=res and req.status=Approved => res.status=DataSent and res.responseData= req.requestedData
}

fact differentRequestDifferentResponse{
	no disj r1,r2:Request| r1.response=r2.response 
}

fact requestApprovedFacts{
	all r: Request,res:Response | r.status in Approved and r.response=Response=>res.status in DataSent
	
}
fact differentUserDifferentData{
	no disj u1,u2:IndividualUser| u1.data=u2.data and
	no disj d1,d2:Data|d1.user=d2.user
}
fact allResponsesAreRelatedToARequest{
}
fact allIndividualRequestsAreRelatedToUser{
	all r:IndividualDataRequest, u:IndividualUser| r.user=u<=>u.requests=r
}

fact checkUsedDrugs{
	all d: UsedDrugs| some c:ChronicDisease| d in c.drugs
}
fact differentRequestDifferentThirdPArty{
	no disj t1,t2: ThirdParty|  #(t1.requests & t2.requests)>0
}

pred show{}
run show for 3
