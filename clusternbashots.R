#NBA Shot Chart Clustering

library(ggplot2)
library(reshape)
library(plyr)

#getting data from directory

a <- lapply(dir("games", full.names = T), function(file){
  print(file)
  tryCatch({
    ans <- read.csv(file, stringsAsFactors=FALSE)
    subset(ans, etype=="shot"&result=="made")
  }, error=function(e){print(e); return(NULL)})
})

aa <- a[unlist(lapply(a, ncol))==32]
b <- do.call(rbind,aa)
b <- b[!is.na(b$x),]
row.names(b) <- NULL

#testing on cleveland

cle <- subset(b, team=="CLE")
plot(cle$x, cle$y)

#looking at the teams/testing out plotting their shot charts

unique(b$team)

qplot(x, y, data = subset(b, team == "CLE"), alpha = I(0.1), size = I(5), main = "Cleveland") + ylim(c(0, 40))
qplot(x, y, data = subset(b, team == "HOU"), alpha = I(0.1), size = I(5), main = "Houston") + ylim(c(0, 40))
qplot(x, y, data = subset(b, team == "TOR"), alpha = I(0.1), size = I(5), main = "Toronto") + ylim(c(0, 40)) + theme_grey(base_size = 17)
qplot(x, y, data = subset(b, team == "ATL"), alpha = I(0.1), size = I(5), main = "Atlanta") + ylim(c(0, 40))

#testing out putting teams shots into matrix form, scaling and plotting

z <- table(cle[c('x', 'y')])
z <- z[as.character(sort(as.numeric(rownames(z)))), as.character(sort(as.numeric(colnames(z))))]
z

zz <- melt(z)
zz <- zz[zz$value > 0, ]
qplot(x, y, data = zz, alpha = value)

#all teams shot charts will be on 51 by 51 "grid", so first remove all outlier shots taken with y>51 (only 10 shots are removed)

allshots <- subset(b, y<52)

#creating the 30 by 2601 matrix, where each row (vector) is a team, which we can run K-means and EM on

teamshot<-matrix(0, nrow=30, ncol=2601)
allshots$team <- as.numeric(as.factor(allshots$team))
for(i in 1:30){
  tmi <- subset(allshots, team==i)
  mati <- table(tmi[c("x", "y")])
  mati <- mati[as.character(sort(as.numeric(rownames(mati)))), as.character(sort(as.numeric(colnames(mati))))]
  
  #filling in matrix with y coordinates (for missing y)
  tstmi <- matrix(0, nrow=nrow(mati), ncol=51)
  colnames(tstmi) <- as.character(1:51)
  for(j in 1: length(colnames(mati))){
    tstmi[,which(colnames(tstmi)==colnames(mati)[j])] <- mati[,j]
  }
  
  #filling in matrix with x coordinates (for missing x)
  tstm2 <- matrix(0, nrow=51, ncol=51)
  rownames(tstm2) <- as.character(1:51)
  for(j in 1: length(rownames(mati))){
    tstm2[which(rownames(tstm2)==rownames(mati)[j]),] <- tstmi[j,]
  }
  
  #scaling, turning into vector, and inserting into overall data matrix
  #tstmsi <- tstm2/max(tstm2)
  tstmsvi <- as.vector(tstm2)
  teamshot[i,] <- tstmsvi
}

#create matrix for probability of making a shot at a spot in a game

teamshotFlip <- ifelse(teamshot>81, 81, teamshot)
teamshotFlip <- teamshotFlip/81

#plot function takes a vector corresponding to each team

plotchart <- function(vec, bern = FALSE){
  plt <- melt(matrix(vec, nrow=51))
  plt <- plt[plt$value > 0,]
  if(bern == FALSE){
    shtchrt <- qplot(X1, X2, data=plt, alpha=value, size=I(5), xlab = "Baseline", ylab = "Sideline") + ylim(c(1, 51)) + xlim(c(1,51))
  } else{
    shtchrt <- qplot(X1, X2, data=plt, alpha=I(1), size=I(5), xlab = "Baseline", ylab = "Sideline") + ylim(c(1, 51)) + xlim(c(1, 51))
  }
  shtchrt
}

#writing the EM-Algorithm for mixture of Bernoulli
#first need to determine a cutoff for what constitutes made or not made

change <- function(vec, thresh){
  vec[which(vec < thresh)] <- 0
  vec[which(vec >= thresh)] <- 1
  return(vec)
}

#set the cutoff for the heatmap at 2 shots made over the course of the year

teamshotEMBern <- apply(teamshotFlip, 2, change, thresh=.025)

#the EM-Algorithm for Bernoulli
#initalize parameters (mu, pi) <- (cluster means, cluster assignment probs)
#E-step: Calculate expected cluster assignments of data given initialized parameters
#M-step: Calculate MLE's for (mu, pi) given both data and expected cluster assignments
#use estimated parameters from M-step in next E-step
#do this recursively until variational lower bound stops increasing by so much

Estep <- function(data, lastpi, lastmu){
  #taking care of zeros to avoid NaN
  lastmu <- ifelse(lastmu==0, 1e-6, lastmu)
  #creating vector for storing log probs per cluster
  z <- c()
  #cluster assignment probability matrix
  temp <- matrix(0, nrow=nrow(data), ncol=length(lastpi))
  #storing cluster assignment probabilities given initialized parameters
  for(n in 1:nrow(data)){
    #log probs per cluster
    for(k in 1:length(lastpi)){
      berns <- c(lastmu[k, c(which(data[n,]==1))], (1 - lastmu[k, c(which(data[n,]==0))]))
      z[k] <- sum(log(berns[which(berns>0)])) + log(lastpi[k])
    }
    M <- max(z)
    temp[n,] <- exp(z - (M + log(sum(exp(z - M)))))
  }
  return(temp)
}

Mstep <- function(data, lastcl){
  #matrix for storing MLE's for mu (cluster means)
  temp <- matrix(0, nrow=ncol(lastcl), ncol=ncol(data))
  #maximizing the log likelihood w.r.t. the cluster means gives their MLE's
  for(i in 1:ncol(lastcl)){
    temp[i,] <- colSums(apply(data, 2, function(x){x*lastcl[,i]}))/sum(lastcl[,i])
  }
  return(temp)
}

VLB <- function(data, lastpi, lastmu){
  #taking care of 0's and 1's to deal with NaN
  lastmu <- ifelse(lastmu==0, 1e-6, lastmu)
  lastmu <- ifelse(lastmu==1, lastmu - (1e-6), lastmu)
  #variational lower bound
  Ffxn <- 0
  #calculating the variational lower bound for after the M-step with given parameters
  for(i in 1:nrow(data)){
    Ffxn <- Ffxn + log(lastpi%*%exp(t(data[i,]%*%t(log(lastmu)) + (1-data[i,])%*%t(log(1-lastmu)))))
  }
  return(Ffxn)
}

EMalg <- function(data, kcl, thresh, labels, seed=100){
  set.seed(seed)
  #initialize parameters
  pi_zed <- rep(1, kcl)/kcl
  mu_zed <- matrix(runif(kcl*ncol(data)), nrow=kcl)
  #E-step
  cl_zed <- Estep(data, pi_zed, mu_zed)
  #M-step
  #MLE for cluster assignment probs are just the averages
  pi_new <- colMeans(cl_zed)
  mu_new <- Mstep(data, cl_zed)
  #variational lower bound
  frengy <- VLB(data, pi_new, mu_new)
  #recurse
  pi_zed <- pi_new
  mu_zed <- mu_new
  cl_zed <- Estep(data, pi_zed, mu_zed)
  pi_new <- colMeans(cl_zed)
  mu_new <- Mstep(data, cl_zed)
  frengy <- c(frengy, VLB(data, pi_new, mu_new))
  while(frengy[length(frengy)]-frengy[length(frengy)-1]>thresh){
    pi_zed <- pi_new
    mu_zed <- mu_new
    cl_zed <- Estep(data, pi_zed, mu_zed)
    pi_new <- colMeans(cl_zed)
    mu_new <- Mstep(data, cl_zed)
    frengy <- c(frengy, VLB(data, pi_new, mu_new))
    print(frengy[length(frengy)])
  }
  res <- list("Evolution of Variational Lower Bound" = frengy, "Cluster Prob" = pi_new, "Cluster Means" = mu_new, "Observation Cluster Probs" = cl_zed)
  rownames(res[[4]]) <- names(table(labels))
  return(res)
}

#testing EM Algorithm on teams for 2 clusters

EM2clust <- EMalg(teamshotEMBern, 2, 1e-10, b$team, seed=50)
plotchart(EM2clust[[3]][1,])
plotchart(EM2clust[[3]][2,])

#kmeans code from Kara
#get training data

shots <- teamshot[1:30,]
labels <- teamshot[,1:2601]

#calculate distance between two vectors

euc_dist <- function(vec1, vec2){
  return(sum((vec1 - vec2)^2))
}

#calculate loss of a cluster and get total loss for all clusters

total_loss <- function(shots, K, kMatrix, shot_label){
  clusterLoss <- 0
  for (k in 1:K){
    kshots <- shots[shot_label == k, ]
    clusterLoss <- clusterLoss + sum(apply(kshots, 1, euc_dist, vec2 = kMatrix[k,]))
  }
  return(clusterLoss)
}


#get new cluster assignments for the rows

new_cluster_label <- function(shots, K, kMatrix){
  apply(shots, 1, function(rowShots){
    which.min(apply(kMatrix, 1, euc_dist, vec2 = rowShots))
  }
  )
}

#create new matrix of parameters for each cluster

new_kMatrix <- function(shots, K, shot_label){
  kMatrix <- array(0, c(K, ncol(shots)))
  
  for (k in 1:K){
    kshots <- shots[shot_label == k, ]
    if (length(kshots) == 0){
      kshots <- shots[sample.int(nrow(shots), size = 1), ]
    }
    if (is.null(dim(kshots))){
      kMatrix[k,] <- kshots
    }
    else{
      kMatrix[k,] <- apply(kshots, 2, mean)
    }
  }
  return(kMatrix)
}

#calculate total distance for each of the clusters

getTotalDist <- function(shots, K, shot_label, kMatrix){
  totalDist <- 0
  for (k in 1:K){
    kshots <- shots[shot_label == k, ]
    if (length(kshots) > 0){
      if (is.null(dim(kshots))){
        totalDist <- totalDist + euc_dist(kshots, vec2 = kMatrix[k, ])
      } else{
        totalDist <- totalDist + sum(apply(kshots, 1, euc_dist, vec2 = kMatrix[k,]))
      }
    }
  }
  return(totalDist)
}


#Function assigns the teams to the K clusters and reassigns until the team no longer changes

my_kmeans_rep <- function(shots, K){
  n <- nrow(shots)
  shot_label_old <- rep(0, n)
  shot_label <- sample(1:K, n, replace = TRUE)
  kMatrix <- new_kMatrix(shots, K, shot_label)
  loss_seq <- c()
  
  while (sum(abs(shot_label - shot_label_old)) > 0.001){
    shot_label_old = shot_label
    shot_label = new_cluster_label(shots, K, kMatrix)
    kMatrix <- new_kMatrix(shots, K, shot_label)
    currentDist <- getTotalDist(shots, K, shot_label, kMatrix)
    loss_seq <- append(loss_seq, currentDist)
  }
  list(
    kMeansLoss = currentDist,
    clusterParameters = kMatrix,
    clusterAssignments = shot_label,
    kMeansLossSeq = loss_seq
  )
}


my_kmeans <- function(shots, K, N, seed = 150){
  set.seed(seed)
  
  bestSolution <- list(kMeansLoss = Inf)
  terminalLossVals <- c()
  for(i in 1:N){
    result <- my_kmeans_rep(shots, K)
    terminalLossVals <- append(terminalLossVals, result$kMeansLoss)
    if(result$kMeansLoss < bestSolution$kMeansLoss){
      bestSolution <- result
    }
  }
  list(
    bestSolution = bestSolution,
    terminalLossVals = terminalLossVals
  )
}

#testing KM Algorithm on teams for 2 clusters
sol2 <- my_kmeans(teamshotFlip, K = 2, N = 15, seed = 150)
plotchart(sol2$bestSolution$clusterParameters[1,])
plotchart(sol2$bestSolution$clusterParameters[2,])

plot(sol2$bestSolution$kMeansLossSeq, main="Loss-Function Evolution for Best Solution K=2", xlab="Iteration", ylab="Loss")
lines(stats::lowess(sol2$bestSolution$kMeansLossSeq))

#creating the player shot matrix

length(unique(allshots$player))
playershot<-matrix(0, nrow=440, ncol=2601)
allshots$player <- as.numeric(as.factor(allshots$player))
for(i in 1:440){
  tmi <- subset(allshots, player==i)
  mati <- table(tmi[c("x", "y")])
  mati <- mati[as.character(sort(as.numeric(rownames(mati)))), as.character(sort(as.numeric(colnames(mati))))]
  
  #filling in matrix with y coordinates (for missing y)
  if(is.matrix(mati)){
    tstmi <- matrix(0, nrow=nrow(mati), ncol=51)
    colnames(tstmi) <- as.character(1:51)
    for(j in 1: length(colnames(mati))){
      tstmi[,which(colnames(tstmi)==colnames(mati)[j])] <- mati[,j]
    }
    
    #filling in matrix with x coordinates (for missing x)
    tstm2 <- matrix(0, nrow=51, ncol=51)
    rownames(tstm2) <- as.character(1:51)
    for(j in 1: length(rownames(mati))){
      tstm2[which(rownames(tstm2)==rownames(mati)[j]),] <- tstmi[j,]
    }  
  } else{
    tstm2 <- matrix(0, nrow=51, ncol=51)
    tstm2[tmi$x,tmi$y] <- 1
  }
  
  #scaling, turning into vector, and inserting into overall data matrix
  #tstmsi <- tstm2/max(tstm2)
  tstmsvi <- as.vector(tstm2)
  playershot[i,] <- tstmsvi
}

#create matrix for probability of making a shot at a spot in a game

playershotFlip <- ifelse(playershot>81, 81, playershot)
playershotFlip <- playershotFlip/81

#set the cutoff for the heatmap at 2 shots made over the course of the year
#create the Bernoulli player shot matrix

playershotEMBern <- apply(playershotFlip, 2, change, thresh=.025)

#testing EM Algorithm on players for 2 clusters
plEM2clust <- EMalg(playershotEMBern, 2, 1e-10, b$player, seed=50)
plotchart(plEM2clust[[3]][1,])
plotchart(plEM2clust[[3]][2,])

#testing KM Algorithm on players for 2 clusters
sol2pl <- my_kmeans(playershotFlip, K = 2, N = 15, seed = 150)
plotchart(sol2pl$bestSolution$clusterParameters[1,])
plotchart(sol2pl$bestSolution$clusterParameters[2,])

#EM for Poisson (DOESN'T WORK)

#I'm not able to get the functions to work. I believe my theory is correct, it's simply that there
#are far too many zeros in the data.  A zero-inflated Poisson, or a Pareto distribution would
#be more appropriate, but I don't think we have the time to code either of those, and the
#plots for using the count data with the K-means algorithm don't look very informative regardless

#initalize parameters (mu, pi) <- (cluster means, cluster assignment probs)
#E-step: Calculate expected cluster assignments of data given initialized parameters
#M-step: Calculate MLE's for (mu, pi) given both data and expected cluster assignments
#use estimated parameters from M-step in next E-step
#do this recursively until variational lower bound stops increasing by so much

EstepPois <- function(data, lastpi, lastmu){
  #taking care of zeros to avoid NaN
  lastmu <- ifelse(lastmu==0, 1e-6, lastmu)
  #creating vector for storing log probs per cluster
  z <- c()
  #cluster assignment probability matrix
  temp <- matrix(0, nrow=nrow(data), ncol=length(lastpi))
  #storing cluster assignment probabilities given initialized parameters
  for(n in 1:nrow(data)){
    #log probs per cluster
    for(k in 1:length(lastpi)){
      poiss <- exp(data[n,]*log(lastmu[k,]) - lastmu[k,] - log(factorial(data[n,])))
      z[k] <- sum(poiss*lastpi[k])
    }
    M <- max(z)
    temp[n,] <- exp(z - (M + log(sum(exp(z - M)))))
  }
  return(temp)
}

MstepPois <- function(data, lastcl){
  #matrix for storing MLE's for mu (cluster means)
  temp <- matrix(0, nrow=ncol(lastcl), ncol=ncol(data))
  #maximizing the log likelihood w.r.t. the cluster means gives their MLE's
  for(i in 1:ncol(lastcl)){
    temp[i,] <- colSums(apply(data, 2, function(x){x*lastcl[,i]}))/sum(lastcl[,i])
  }
  return(temp)
}

VLBPois <- function(data, lastpi, lastmu){
  #taking care of 0's
  lastmu <- ifelse(lastmu==0, 1e-6, lastmu)
  #variational lower bound
  Ffxn <- 0
  #calculating the variational lower bound for after the M-step with given parameters
  for(i in 1:nrow(data)){
    for(k in 1:length(lastpi)){
      Ffxn <- Ffxn + lastpi[k]*(exp((data[i,]%*%t(log(lastmu)))[k] - sum(lastmu[k,]) - sum(log(factorial(data[i,])))))
    }
  }
  return(Ffxn)
}

EMalgPois <- function(data, kcl, thresh, labels, seed=100){
  set.seed(seed)
  #initialize parameters
  pi_zed <- rep(1, kcl)/kcl
  mu_zed <- matrix(rpois(kcl*ncol(data), 1), nrow=kcl)
  #E-step
  cl_zed <- EstepPois(data, pi_zed, mu_zed)
  #M-step
  #MLE for cluster assignment probs are just the averages
  pi_new <- colMeans(cl_zed)
  mu_new <- MstepPois(data, cl_zed)
  #variational lower bound
  frengy <- VLBPois(data, pi_new, mu_new)
  #recurse
  pi_zed <- pi_new
  mu_zed <- mu_new
  cl_zed <- EstepPois(data, pi_zed, mu_zed)
  pi_new <- colMeans(cl_zed)
  mu_new <- MstepPois(data, cl_zed)
  frengy <- c(frengy, VLBPois(data, pi_new, mu_new))
  while(frengy[length(frengy)]-frengy[length(frengy)-1]>thresh){
    pi_zed <- pi_new
    mu_zed <- mu_new
    cl_zed <- EstepPois(data, pi_zed, mu_zed)
    pi_new <- colMeans(cl_zed)
    mu_new <- MstepPois(data, cl_zed)
    frengy <- c(frengy, VLBPois(data, pi_new, mu_new))
    print(frengy[length(frengy)])
  }
  res <- list("Evolution of Variational Lower Bound" = frengy, "Cluster Prob" = pi_new, "Cluster Means" = mu_new, "Observation Cluster Probs" = cl_zed)
  rownames(res[[4]]) <- names(table(labels))
  return(res)
}

#loading in Team Stats for the 2009-2010 season

TeamStats0910 <- read.csv("0910TeamStats.csv")
TeamStats0910 <- arrange(TeamStats0910, Team)
TeamStats0910$Team <- names(table(b$team))

#putting on team wins
#found records online and ordered by name

W <- c(53,50,44,41,61,55,53,27,26,42,32,29,57,40,47,46,15,12,37,29,50,59,27,54,50,25,50,40,53,26)
TeamStats0910 <- cbind(TeamStats0910, W)


#loading in Player Stats for the 2009-2010 season
PlayerStats0910 <- read.csv("0910PlayerStats.csv")

#give all players with 2 positions their primary position

PlayerStats0910$Pos[which(PlayerStats0910$Pos=="C-PF")] <- "C"
PlayerStats0910$Pos[which(PlayerStats0910$Pos=="PF-C")] <- "PF"
PlayerStats0910$Pos[which(PlayerStats0910$Pos=="PF-SF")] <- "PF"
PlayerStats0910$Pos[which(PlayerStats0910$Pos=="PG-SG")] <- "PG"
PlayerStats0910$Pos[which(PlayerStats0910$Pos=="SF-SG")] <- "SF"
PlayerStats0910$Pos[which(PlayerStats0910$Pos=="SG-PF")] <- "SG"
PlayerStats0910$Pos[which(PlayerStats0910$Pos=="SG-PG")] <- "SG"
PlayerStats0910$Pos[which(PlayerStats0910$Pos=="SG-SF")] <- "SG"
PlayerStats0910$Pos <- droplevels(PlayerStats0910$Pos)
table(PlayerStats0910$Pos)

##Results
#Teams
#Two Clusters, Team Bernoulli, K-Means, seed = 100, N = 15

KM2KTB <- my_kmeans(teamshotEMBern, K = 2, N = 15, seed = 100)
plotchart(KM2KTB$bestSolution$clusterParameters[1,]) + theme_grey(base_size = 17) + ggtitle("Cluster 1")
plotchart(KM2KTB$bestSolution$clusterParameters[2,]) + theme_grey(base_size = 17) + ggtitle("Cluster 2")
KM2KTBCLAS <- cbind(names(table(b$team)), KM2KTB$bestSolution$clusterAssignments, TeamStats0910$X3P, TeamStats0910$PTS.G, TeamStats0910$W)
colnames(KM2KTBCLAS) <- c("team", "clust", "X3P", "PPG", "W")
KM2KTBCLAS <- as.data.frame(KM2KTBCLAS)
KM2KTBCLAS$clust <- as.factor(KM2KTBCLAS$clust)
KM2KTBCLAS$X3P <- as.numeric(levels(KM2KTBCLAS$X3P))[KM2KTBCLAS$X3P]
KM2KTBCLAS$PPG <- as.numeric(levels(KM2KTBCLAS$PPG))[KM2KTBCLAS$PPG]
KM2KTBCLAS$W <- as.numeric(levels(KM2KTBCLAS$W))[KM2KTBCLAS$W]
fitK2T3 <- aov(X3P ~ clust, data = KM2KTBCLAS)
fitK2TP <- aov(PPG ~ clust, data = KM2KTBCLAS)
fitK2TW <- aov(W ~ clust, data = KM2KTBCLAS)
summary(fitK2T3)
summary(fitK2TP)
summary(fitK2TW)

#significant difference found in 3 pointers made

TukeyHSD(fitK2T3)
KM2KTBCPR <- c(length(which(KM2KTBCLAS$clust == 1))/30, length(which(KM2KTBCLAS$clust == 2))/30)
KM2KTBCPR

#cluster 2 is made up of teams that score more 3 pointers than cluster 1
#there are half the teams (15) in cluster 1 and half the teams in cluster 2


#Two Clusters, Team Bernoulli, EM, seed = 100, thresh = 1e-6

EM2KTB <- EMalg(teamshotEMBern, kcl = 2, thresh = 1e-6, labels = b$team, seed = 100)
plotchart(EM2KTB[[3]][1,])
plotchart(EM2KTB[[3]][2,])
toph <- subset(melt(EM2KTB[[4]]), round(melt(EM2KTB[[4]])$value) !=0)
toph <- toph[,-3]
row.names(toph) <- NULL
toph <- arrange(toph, X1)
EM2KTBCLAS <- cbind(toph, TeamStats0910$X3P, TeamStats0910$PTS.G, TeamStats0910$W)
colnames(EM2KTBCLAS) <- c("team", "clust", "X3P", "PPG", "W")
EM2KTBCLAS <- as.data.frame(EM2KTBCLAS)
EM2KTBCLAS$clust <- as.factor(EM2KTBCLAS$clust)
fitE2T3 <- aov(X3P ~ clust, data = EM2KTBCLAS)
fitE2TP <- aov(PPG ~ clust, data = EM2KTBCLAS)
fitE2TW <- aov(W ~ clust, data = EM2KTBCLAS)
summary(fitE2T3)
summary(fitE2TP)
summary(fitE2TW)

EM3KTBCPR <- EM2KTB[[2]]
EM3KTBCPR

#there are 13.3% of teams (4) in cluster 1, and 86.67% of teams (26) in cluster 2


#Three Clusters, Team Bernoulli, K-Means, seed = 100, N = 15

KM3KTB <- my_kmeans(teamshotEMBern, K = 3, N = 15, seed = 100)
plotchart(KM3KTB$bestSolution$clusterParameters[1,]) + theme_grey(base_size = 17) + ggtitle("Cluster 1")
plotchart(KM3KTB$bestSolution$clusterParameters[2,]) + theme_grey(base_size = 17) + ggtitle("Cluster 2")
plotchart(KM3KTB$bestSolution$clusterParameters[3,]) + theme_grey(base_size = 17) + ggtitle("Cluster 3")
KM3KTBCLAS <- cbind(names(table(b$team)), KM3KTB$bestSolution$clusterAssignments, TeamStats0910$X3P, TeamStats0910$PTS.G, TeamStats0910$W)
colnames(KM3KTBCLAS) <- c("team", "clust", "X3P", "PPG", "W")
KM3KTBCLAS <- as.data.frame(KM3KTBCLAS)
KM3KTBCLAS$clust <- as.factor(KM3KTBCLAS$clust)
KM3KTBCLAS$X3P <- as.numeric(levels(KM3KTBCLAS$X3P))[KM3KTBCLAS$X3P]
KM3KTBCLAS$PPG <- as.numeric(levels(KM3KTBCLAS$PPG))[KM3KTBCLAS$PPG]
KM3KTBCLAS$W <- as.numeric(levels(KM3KTBCLAS$W))[KM3KTBCLAS$W]
fitK3T3 <- aov(X3P ~ clust, data = KM3KTBCLAS)
fitK3TP <- aov(PPG ~ clust, data = KM3KTBCLAS)
fitK3TW <- aov(W ~ clust, data = KM3KTBCLAS)
summary(fitK3T3)
summary(fitK3TP)
summary(fitK3TW)

#significant differences in 3 pointers and points per game

TukeyHSD(fitK3T3)
TukeyHSD(fitK3TP)
KM3KTBCPR <- c(length(which(KM3KTBCLAS$clust == 1))/30, length(which(KM3KTBCLAS$clust == 2))/30, length(which(KM3KTBCLAS$clust == 3))/30)
KM3KTBCPR

#cluster 1 scores significantly more 3 pointers than cluster 2 and cluster 3, there is no significant difference b/w 2 and 3
#cluster 1 socres significantly more points per game than cluster 2 and cluster 3, there is no significant difference b/w 2 and 3
#there are 30% of the teams (9) in cluster 1, 33.33% (10) in cluster 2, and 36.67% (11) in cluster 3


#Three Clusters, Team Bernoulli, EM, seed = 100, thresh = 1e-6

EM3KTB <- EMalg(teamshotEMBern, kcl = 3, thresh = 1e-6, labels = b$team, seed = 100)
plotchart(EM3KTB[[3]][1,]) + theme_grey(base_size = 17) + ggtitle("Cluster 1")
plotchart(EM3KTB[[3]][2,]) + theme_grey(base_size = 17) + ggtitle("Cluster 2")
plotchart(EM3KTB[[3]][3,]) + theme_grey(base_size = 17) + ggtitle("Cluster 3")
mako <- subset(melt(EM3KTB[[4]]), round(melt(EM3KTB[[4]])$value) !=0)
mako <- mako[,-3]
row.names(mako) <- NULL
mako <- arrange(mako, X1)
EM3KTBCLAS <- cbind(mako, TeamStats0910$X3P, TeamStats0910$PTS.G, TeamStats0910$W)
colnames(EM3KTBCLAS) <- c("team", "clust", "X3P", "PPG", "W")
EM3KTBCLAS <- as.data.frame(EM3KTBCLAS)
EM3KTBCLAS$clust <- as.factor(EM3KTBCLAS$clust)
fitE3T3 <- aov(X3P ~ clust, data = EM3KTBCLAS)
fitE3TP <- aov(PPG ~ clust, data = EM3KTBCLAS)
fitE3TW <- aov(W ~ clust, data = EM3KTBCLAS)
summary(fitE3T3)
summary(fitE3TP)
summary(fitE3TW)

#significant differences in ppg

TukeyHSD(fitE3TP)
EM3KTBCPR <- EM3KTB[[2]]
EM3KTBCPR

#cluster 2 scores significantly more points than cluster 1, no other significant differences
#there are 93.33% (28) teams in cluster 1, and 3.33% (1) team each in cluster 2 and 3


#Players
#Two Clusters, Players Bernoulli, K-Means, seed = 100, N = 15

KM2KPB <- my_kmeans(playershotEMBern, K = 2, N = 15, seed = 100)
plotchart(KM2KPB$bestSolution$clusterParameters[1,])
plotchart(KM2KPB$bestSolution$clusterParameters[2,])
plot(KM2KPB$bestSolution$kMeansLossSeq, main="Loss-Function Evolution for Best Solution K=2", xlab="Iteration", ylab="Loss", pch = 16, cex = 2)
KM2KPBCLAS <- cbind(names(table(b$player)), KM2KPB$bestSolution$clusterAssignments, PlayerStats0910$Pos, PlayerStats0910$X3P, PlayerStats0910$FG)
colnames(KM2KPBCLAS) <- c("player", "clust", "pos", "X3P", "FG")
KM2KPBCLAS <- as.data.frame(KM2KPBCLAS)
KM2KPBCLAS$clust <- as.factor(KM2KPBCLAS$clust)
KM2KPBCLAS$pos <- PlayerStats0910$Pos
KM2KPBCLAS$X3P <- as.numeric(levels(KM2KPBCLAS$X3P))[KM2KPBCLAS$X3P]
KM2KPBCLAS$FG <- as.numeric(levels(KM2KPBCLAS$FG))[KM2KPBCLAS$FG]

table2 <- table(KM2KPBCLAS$clust, KM2KPBCLAS$pos)
table2

fitK2PP <- chisq.test(table2)
fitK2P3 <- aov(X3P ~ clust, data = KM2KPBCLAS)
fitK2PF <- aov(FG ~ clust, data = KM2KPBCLAS)
fitK2PP
summary(fitK2P3)
summary(fitK2PF)

#significant difference in field goals

TukeyHSD(fitK2PF)
KM2KPBCPR <- c(length(which(KM2KPBCLAS$clust == 1))/440, length(which(KM2KPBCLAS$clust == 2))/440)
KM2KPBCPR

#cluster 1 makes significantly more field goals than cluster 2
#there are 16.82% (74) players in cluster 1, and 83.18% (366) players in cluster 2


#Two Clusters, Players Bernoulli, EM, seed = 100, thresh = 1e-6

EM2KPB <- EMalg(playershotEMBern, kcl = 2, thresh = 1e-6, labels = b$player, seed = 100)
plotchart(EM2KPB[[3]][1,])
plotchart(EM2KPB[[3]][2,])
plot(EM2KPB[[1]], main="VLB Evolution for EM (Players) K=2", xlab="Iteration", ylab="Variational Free Energy", pch = 16, cex = 1.2)
wulf <- subset(melt(EM2KPB[[4]]), round(melt(EM2KPB[[4]])$value) !=0)
wulf <- wulf[,-3]
row.names(wulf) <- NULL
wulf <- arrange(wulf, X1)
EM2KPBCLAS <- cbind(wulf, PlayerStats0910$Pos, PlayerStats0910$X3P, PlayerStats0910$FG)
colnames(EM2KPBCLAS) <- c("player", "clust", "pos", "X3P", "FG")
EM2KPBCLAS <- as.data.frame(EM2KPBCLAS)
EM2KPBCLAS$clust <- as.factor(EM2KPBCLAS$clust)

table3 <- table(EM2KPBCLAS$clust, EM2KPBCLAS$pos)
table3

fitE2PP <- chisq.test(table3)
fitE2P3 <- aov(X3P ~ clust, data = EM2KPBCLAS)
fitE2PF <- aov(FG ~ clust, data = EM2KPBCLAS)
fitE2PP
summary(fitE2P3)
summary(fitE2PF)

EM2KPBCPR <- colSums(round(EM2KPB[[4]]))/440
EM2KPBCPR

#there are 7.27% (32) players in cluster 1, and 92.73% (408) in cluster 2


#Three Clusters, Players Bernoulli, K-Means, seed = 100, N = 15

KM3KPB <- my_kmeans(playershotEMBern, K = 3, N = 15, seed = 100)
plotchart(KM3KPB$bestSolution$clusterParameters[1,])
plotchart(KM3KPB$bestSolution$clusterParameters[2,])
plotchart(KM3KPB$bestSolution$clusterParameters[3,])
plot(KM3KPB$bestSolution$kMeansLossSeq, main="Loss-Function Evolution for Best Solution K=3", xlab="Iteration", ylab="Loss", pch = 16, cex = 2)
KM3KPBCLAS <- cbind(names(table(b$player)), KM3KPB$bestSolution$clusterAssignments, PlayerStats0910$Pos, PlayerStats0910$X3P, PlayerStats0910$FG)
colnames(KM3KPBCLAS) <- c("player", "clust", "pos", "X3P", "FG")
KM3KPBCLAS <- as.data.frame(KM3KPBCLAS)
KM3KPBCLAS$clust <- as.factor(KM3KPBCLAS$clust)
KM3KPBCLAS$pos <- PlayerStats0910$Pos
KM3KPBCLAS$X3P <- as.numeric(levels(KM3KPBCLAS$X3P))[KM3KPBCLAS$X3P]
KM3KPBCLAS$FG <- as.numeric(levels(KM3KPBCLAS$FG))[KM3KPBCLAS$FG]

table0 <- table(KM3KPBCLAS$clust, KM3KPBCLAS$pos)
table0

fitK3PP <- chisq.test(table0)
fitK3P3 <- aov(X3P ~ clust, data = KM3KPBCLAS)
fitK3PF <- aov(FG ~ clust, data = KM3KPBCLAS)
fitK3PP
summary(fitK3P3)
summary(fitK3PF)

#significant differences in field goals made

TukeyHSD(fitK3PF)
KM3KPBCPR <- c(length(which(KM3KPBCLAS$clust == 1))/440, length(which(KM3KPBCLAS$clust == 2))/440, length(which(KM3KPBCLAS$clust == 3))/440)
KM3KPBCPR

#cluster 3 scores significantly more field goals than cluster 2, no other significant differences
#there are 11.14% of the players (49) in cluster 1, 72.04% (317) in cluster 2, and 16.82% (74) in cluster 3


#Three Clusters, Players Bernoulli, EM, seed = 100, thresh = 1e-6

EM3KPB <- EMalg(playershotEMBern, kcl = 3, thresh = 1e-6, labels = b$player, seed = 100)
plotchart(EM3KPB[[3]][1,]) + theme_grey(base_size = 17) + ggtitle("Cluster 1")
plotchart(EM3KPB[[3]][2,]) + theme_grey(base_size = 17) + ggtitle("Cluster 2")
plotchart(EM3KPB[[3]][3,]) + theme_grey(base_size = 17) + ggtitle("Cluster 3")
plot(EM3KPB[[1]], main="VLB Evolution for EM (Players) K=3", xlab="Iteration", ylab="Variational Free Energy", pch = 16, cex = 1)
duck <- subset(melt(EM3KPB[[4]]), round(melt(EM3KPB[[4]])$value) !=0)
duck <- duck[,-3]
row.names(duck) <- NULL
duck <- arrange(duck, X1)
EM3KPBCLAS <- cbind(duck, PlayerStats0910$Pos, PlayerStats0910$X3P, PlayerStats0910$FG)
colnames(EM3KPBCLAS) <- c("player", "clust", "pos", "X3P", "FG")
EM3KPBCLAS <- as.data.frame(EM3KPBCLAS)
EM3KPBCLAS$clust <- as.factor(EM3KPBCLAS$clust)

table1 <- table(EM3KPBCLAS$clust, EM3KPBCLAS$pos)
table1

fitE3PP <- chisq.test(table1)
fitE3P3 <- aov(X3P ~ clust, data = EM3KPBCLAS)
fitE3PF <- aov(FG ~ clust, data = EM3KPBCLAS)
fitE3PP
summary(fitE3P3)
summary(fitE3PF)

#significant differences in 3 pointers and field goals

TukeyHSD(fitE3P3)
TukeyHSD(fitE3PF)
EM3KPBCPR <- colSums(round(EM3KPB[[4]]))/440
EM3KPBCPR

#cluster 1 makes significantly more 3 pointers than cluster 2 and cluster 3, no other significant differences
#cluster 1 makes significantly more field goals than cluster 2 and cluster 3, no other significant differences
#there are 40.23% (177) players in cluster 1, 52.27% (230) in cluster 2, and 7.5% (33) in cluster 3


#Four Clusters, Players Bernoulli, K-Means, seed = 100, N = 15

KM4KPB <- my_kmeans(playershotEMBern, K = 4, N = 15, seed = 100)
plotchart(KM4KPB$bestSolution$clusterParameters[1,])
plotchart(KM4KPB$bestSolution$clusterParameters[2,])
plotchart(KM4KPB$bestSolution$clusterParameters[3,])
plotchart(KM4KPB$bestSolution$clusterParameters[4,])
plot(KM4KPB$bestSolution$kMeansLossSeq, main="Loss-Function Evolution for Best Solution K=4", xlab="Iteration", ylab="Loss", pch = 16, cex = 2)
KM4KPBCLAS <- cbind(names(table(b$player)), KM4KPB$bestSolution$clusterAssignments, PlayerStats0910$Pos, PlayerStats0910$X3P, PlayerStats0910$FG)
colnames(KM4KPBCLAS) <- c("player", "clust", "pos", "X3P", "FG")
KM4KPBCLAS <- as.data.frame(KM4KPBCLAS)
KM4KPBCLAS$clust <- as.factor(KM4KPBCLAS$clust)
KM4KPBCLAS$pos <- PlayerStats0910$Pos
KM4KPBCLAS$X3P <- as.numeric(levels(KM4KPBCLAS$X3P))[KM4KPBCLAS$X3P]
KM4KPBCLAS$FG <- as.numeric(levels(KM4KPBCLAS$FG))[KM4KPBCLAS$FG]

table4 <- table(KM4KPBCLAS$clust, KM4KPBCLAS$pos)
table4

fitK4PP <- chisq.test(table4)
fitK4P3 <- aov(X3P ~ clust, data = KM4KPBCLAS)
fitK4PF <- aov(FG ~ clust, data = KM4KPBCLAS)
fitK4PP
summary(fitK4P3)
summary(fitK4PF)

#significant differences in 3 pointers and field goals made

TukeyHSD(fitK4P3)
TukeyHSD(fitK4PF)
KM4KPBCPR <- c(length(which(KM4KPBCLAS$clust == 1))/440, length(which(KM4KPBCLAS$clust == 2))/440, length(which(KM4KPBCLAS$clust == 3))/440, length(which(KM4KPBCLAS$clust == 4))/440)
KM4KPBCPR

#cluster 3 scores significantly more 3 pointers than clusters 2 and 4,  no other significant differences
#cluster 4 scores significantly more field goals than cluster 2, no other significant differences
#there are 9.8% (43) of players in cluster 1, 67.9% (299) in cluster 2, 8.9% (39) in cluster 3, and 13.4% (59) in cluster 4


#Four Clusters, Players Bernoulli, EM, seed = 100, thresh = 1e-6

EM4KPB <- EMalg(playershotEMBern, kcl = 4, thresh = 1e-6, labels = b$player, seed = 100)
plotchart(EM4KPB[[3]][1,])
plotchart(EM4KPB[[3]][2,])
plotchart(EM4KPB[[3]][3,])
plotchart(EM4KPB[[3]][4,])
plot(EM4KPB[[1]], main="VLB Evolution for EM (Players) K=4", xlab="Iteration", ylab="Variational Free Energy", pch = 16, cex = 1.2)
hill <- subset(melt(EM4KPB[[4]]), round(melt(EM4KPB[[4]])$value) !=0)
hill <- hill[,-3]
row.names(hill) <- NULL
hill <- arrange(hill, X1)
EM4KPBCLAS <- cbind(hill, PlayerStats0910$Pos, PlayerStats0910$X3P, PlayerStats0910$FG)
colnames(EM4KPBCLAS) <- c("player", "clust", "pos", "X3P", "FG")
EM4KPBCLAS <- as.data.frame(EM4KPBCLAS)
EM4KPBCLAS$clust <- as.factor(EM4KPBCLAS$clust)

table5 <- table(EM4KPBCLAS$clust, EM4KPBCLAS$pos)
table5

fitE4PP <- chisq.test(table5)
fitE4P3 <- aov(X3P ~ clust, data = EM4KPBCLAS)
fitE4PF <- aov(FG ~ clust, data = EM4KPBCLAS)
fitE4PP
summary(fitE4P3)
summary(fitE4PF)

#significant difference in field goals

TukeyHSD(fitE4PF)
EM4KPBCPR <- colSums(round(EM4KPB[[4]]))/440
EM4KPBCPR

#cluster 2 makes significantly more field goals than cluster 4, no other significant differences
#there are 10.2% (45) of players in cluster 1, 0.5% (2) in cluster 2, 1.8% (8) in cluster 3, and 87.5% (385) in cluster 4
