open util/integer

 sig Time{
		date: one Int,
		hour: one Int,
		minutes: one Int
}
{ hour >=0 and hour<=5 and
	minutes >=0 and minutes<=5 and
	date>=1 and date <=5
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
	--preConfirmedThirdParties: set ThirdParty,
	--receivedRequests: set IndividualDataRequest,
	--participatedOrganizations:set RunningOrganization,
	--spectatedOrganizations: set RunningOrganization		
}

sig ThirdParty{
	--requests: set Request,
	services: set Service,
	--organizations: set RunningOrganization,
	address: one Location
}

abstract sig Service{}
one sig AutomatedSOS extends Service{}
one sig Track4Run extends Service{}


sig SosNotification{
	sender: one IndividualUser,
	receiver:one ThirdParty,
	healthData: one HealthData,
	locationData:one LocationData
}
{
	--Time of healthData and locationData must be the same
	healthData.receiveTime=locationData.receiveTime and 
	--Notification should only be sent when healt values are out of range
	(healthData.heartBeat<10 or healthData.heartBeat>15) and
	healthData in sender.data and
	locationData in sender.data
}


--Every user's data should be specific
fact differentUserDifferentData{
	no disj u1,u2:IndividualUser| u1.data=u2.data 
}

fact bidirectionalRelationBetweenDataAndUser{
	all d:Data,u:IndividualUser| d.user=u iff d in u.data
}
--Every usedDrugs should be related with at least one disease
fact checkUsedDrugs{
	all d: UsedDrugs| some c:ChronicDisease| d in c.drugs
}

--Each user should has only one ProfileData
fact eachUserHasOnlyOneProfileData{
	all u:IndividualUser| #(ProfileData & u.data)=1
}


--<<<<<<<<<<<<<<<<<<<<<<<<<<<<<AutomatedSOS Facts start>>>>>>>>>>>>>>>>>>>

--All AutomatedSOS users should have location and health data
fact sosUserShouldHaveLocationAndHealthData{
	all u:IndividualUser, s:AutomatedSOS| #(u.services&s)=1 => some l:LocationData, h:HealthData| l.receiveTime=h.receiveTime and l.user=u and h.user=u
}
--sender of notification must be AutomatedSosUser
fact senderMustBeSosUser{
	all n:SosNotification, u:IndividualUser| n.sender=u=> #(u.services&AutomatedSOS)=1
}
--receiver of notification must be AutomatedSosUser
fact receiverMustBeSosUser{
	all n:SosNotification, t:ThirdParty| n.receiver=t => #(t.services&AutomatedSOS)=1
}

fact forEveryExceedOfThresholdOnlyOneNotificationMustBeSent{
	no disj n1,n2: SosNotification|  #(n1.healthData & n2.healthData)>0 
}

--<<<<<<<<<<<<<<<<<<<<<<<<<<<<<AutomatedSOS Facts end>>>>>>>>>>>>>>>>>>>



pred showSosUsers{
	#( SosNotification)=2 and
	#(IndividualUser) =2
	and all u:IndividualUser| #(u.data&HealthData)=1
}
assert checkExceedingLimits{
	no n:SosNotification| (n.healthData.heartBeat=11)
}
check checkExceedingLimits
run showSosUsers for 60
run showSosUsers
