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


sig IndividualUser{
	data:some Data,
	services: set Service,
	preConfirmedThirdParties: set ThirdParty,
	--receivedRequests: set IndividualDataRequest,
	participatedOrganizations:set RunningOrganization,
	spectatedOrganizations: set RunningOrganization		
}

sig ThirdParty{
	--requests: set Request,
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
	time: one Time,
	locationData:some LocationData
}
{	 this in organizer.organizations
}

sig Path{
	organization:RunningOrganization,
	startLocation: one Location,
	intermediaryLocation: one Location,
	endLocation: one Location
}
{
	no l: intermediaryLocation | startLocation=l or endLocation=l
}

--Every user's data should be specific
fact differentUserDifferentData{
	no disj u1,u2:IndividualUser| u1.data=u2.data 
}

fact bidirectionalRelationBetweenDataAndUser{
	all d:Data,u:IndividualUser| d.user=u iff d in u.data
}


--User can't enroll a run as a both spectator and runner
fact userCantEnrollAsSpectatorToParticipatedRun{
	all u:IndividualUser| #(u.participatedOrganizations & u.spectatedOrganizations)=0
}
--Spectators and runners of a run is all different
fact runnerSpectatorRelation{
	all r:RunningOrganization| #(r.spectators & r.runners)=0
}
--All runners in a run must participate it
fact runnerUserRelation{
	all r:RunningOrganization, u:IndividualUser| u in r.runners iff r in u.participatedOrganizations
}
--All spectators in a run must spectate it
fact spectatorUserRelation{
	all r:RunningOrganization, u:IndividualUser| u in r.spectators iff r in u.spectatedOrganizations
}
-- All organizations must be in the list of it's organizer
fact organizationOrganizerRelation{
	all  r: RunningOrganization, t:ThirdParty| r in t.organizations iff r.organizer=t
}
--Each run has it's specific path
fact differentRunDifferentPath{
	no disj o1,o2:RunningOrganization| o1.path=o2.path
}
fact organizationPathRelation{
	all  r: RunningOrganization, p:Path| r=p.organization iff r.path=p
}
--Organizer of run should activate Track4run
fact organizerTrack4RunConstraint{
	all t:ThirdParty, tr:Track4Run| #(t.organizations)>0 iff tr in t.services
}
--Runner should activate Track4Run
fact runnerTrack4RunConstraint{
	all t:IndividualUser | #(t.participatedOrganizations)>0 iff Track4Run in t.services
}
--Runner should have at least 1 locationData
fact runnerLocationDataConstraint{
	all t:IndividualUser| some l:LocationData| #(t.participatedOrganizations)>0 => t.data=l
}
--#LocationData and  #Runners should be equal in Organization
fact locationNumberAndRunnerConstraint{
	all o:RunningOrganization|#(o.runners)=#(o.locationData)
}

--Organization should access to it's runners' location. So, spectators and organizers can access it
fact organizationShouldHaveLocationDataOfRunners{
	all r:RunningOrganization, u:IndividualUser| u in r.runners implies one l:LocationData| l.user=u and l in r.locationData
}
fact differentOrganizationDifferentData{
	no disj r1,r2: RunningOrganization|  #(r1.locationData & r2.locationData)>0
}
pred showForTrack4Run{}
--run showForTrack4Run for 3 but 2 RunningOrganization



assert  isThereUserEnrolledAnOrganizationAsSpectatorAndParticipator{
	no u:IndividualUser| #(u.spectatedOrganizations & u.participatedOrganizations) >0
}
assert someOrganizationsDoesntHaveAllRunnersData{
	all o:RunningOrganization, u:IndividualUser| u in o.runners => (u.data & LocationData)  in o.locationData
}
--check isThereUserEnrolledAnOrganizationAsSpectatorAndParticipator
check someOrganizationsDoesntHaveAllRunnersData
