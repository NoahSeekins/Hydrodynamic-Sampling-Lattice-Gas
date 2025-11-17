#include <stdlib.h>
#include <unistd.h>
#include <stdio.h>
#include <string.h>
#include <math.h>
#include <mygraph.h>
#include <time.h>
#include <gsl/gsl_rng.h>
#include <gsl/gsl_randist.h>

//
// Define Dimension and Velocities

#define dim 300
#define V 3

// Initialize Array and Parameters

int n[dim][V];

double Nav = 1000;

int Nleft[V], Nadd[V];

double w[V] = {1. / 6., 2. / 3., 1. / 6.};
double vel[V] = {-1, 0, 1};

int iterations = 0;

// System Variables

int DIM = dim; // required for graphics to function

double omega = 1;
int Seed = 0;

double NBarEqSin = 1000, amp = 10;
double NBarl = 1000, NBarr = 500, uG = 0;

double NData[dim], JData[dim], PiData[dim];

// Initialize Sample Structure
typedef struct
{
  int pihalf /*, piquarter, pi3quarter*/;
  double Sumhalf, Loghalf /*, Sumquarter, Logquarter, Sum3quarter, Log3quarter*/;
} PiArray_t;
PiArray_t **Lookup; // max J value
// You need one array for each w[i] size, i.e. 3 for D2Q9

int Nmax = 1100, LookupTable = 0;

// Initialize Pi Dist Structure
typedef struct
{
  int size;
  double *array;
} piArr;
piArr piDistribution; // For the cumulative local equilibrium pi distribution
piArr CumDist;        // For the cumulative local equilibrium pi distribution
piArr CumInv;         // For the reverse cumulative local equilibrium pi distribution

// GSL Setup

const gsl_rng_type *TYPE;
gsl_rng *RANDOM;

int GSL(int N, double p)
{
  int b = gsl_ran_binomial(RANDOM, p, N);
  return b;
}

// Create and Destroy the Lookup tables

void DestroyLookupTable(int Nmax)
{
  LookupTable = 0;
  for (int n = 0; n < Nmax; n++)
  {
    free(Lookup[n]);
  }
  free(Lookup);
}

void GenerateLookupTable(int Nmax)
{
  LookupTable = 1;
  Lookup = malloc(Nmax * sizeof(PiArray_t *));
  if (Lookup == NULL)
    printf("Lookup Not Assigned\n");
  for (int n = 0; n < Nmax; n++)
  {
    Lookup[n] = malloc((n + 1) * sizeof(PiArray_t));
    if (Lookup[n] == NULL)
      printf("Lookup[n] Not Assigned\n");
    for (int j = 0; j < n + 1; j++)
    {
      Lookup[n][j].pihalf = -1;
      // now will the Lookup[n][j].xx with the actual data
    }
  }
}

// Distribution Sampling
int poissonLog(double lam)
{
  double r = (double)rand() / RAND_MAX;
  double LPois = -lam;
  int p = 0;
  double Sum = exp(LPois);
  while (r >= Sum)
  {
    p++;
    LPois += log(lam / p);
    Sum += exp(LPois);
  }
  return p;
}

int binomialLog(int N, double p)
{
  double q = 1 - p;
  double r = (double)rand() / RAND_MAX;
  if (r >= 1)
    return N;
  if (r <= 0)
    return 0;
  double LBin = N * log(q);
  double Sum = exp(LBin);
  int b = 0;
  while (r >= Sum)
  {
    b++;
    if (b > N)
      printf("b>N");
    LBin += log(p / q * (N - b + 1) / b);
    Sum += exp(LBin);
  }
  return b;
}

int pidistsampling(int N, int J)
{
  // System Variables
  double p = 0.125;
  double Sum = 1, Log = 0;
  int pi = J;
  // sampling procedure
  double r = (double)rand() / RAND_MAX;
  if (r <= 0)
    return J;
  else if (r >= 1)
    return N;
  else if (J + 2 > N)
    return J;
  else
  {
    while (pi < N)
    {
      Log += log((double)2 * p * (N - pi) * (N - pi - 1) / ((pi + 2) * (pi + 2) - J * J));
      Sum += exp(Log);
      pi = pi + 2;
    }
    pi = J;
    Log = -log(Sum);
    Sum = exp(Log);
    while (r > Sum)
    {
      Log += log((double)2 * p * (N - pi) * (N - pi - 1) / ((pi + 2) * (pi + 2) - J * J));
      Sum += exp(Log);
      pi = pi + 2;
      // debug failsafe
      if (pi > N)
        printf("\npi>N");
    }
    return pi;
  }
}

// Lookup Methods

// Generate the central value of the pi distribution for a given N and J
void PiGenerate(int N, int NMax, int J)
{
  // System Variables
  double p = 0.125; // TODO: Change to prob array
  double Sum = 1, Log = 0;
  int pi, piStart;
  if (N == 0)
  {
    piStart = 0;
  }
  else if (((N / 3) % 2 == abs(J) % 2))
  {
    piStart = (double)N / 3; // approximate the central value for pi
  }
  else
  {
    piStart = (double)N / 3 - 1; // if out of parity, decrease by one
  }
  if (piStart < abs(J))
  {
    piStart = abs(J); // safeguard for low densities where N/3 could be <J
  }
  pi = piStart;
  while (pi < NMax)
  {
    if (pi > N)
      // debug failsafe
      printf("\npi>N");
    // Log(P(pi+2))
    Log += log((double)2 * p * (N - pi) * (N - pi - 1) / ((pi + 2) * (pi + 2) - J * J));
    // C(pi+2)
    Sum += exp(Log);
    pi = pi + 2;
  }
  pi = piStart;
  Log = 0;
  double SumMin = 1;
  while (pi >= abs(J))
  {
    if (pi < J)
      // debug failsafe
      printf("\npi<J");
    pi = pi - 2;
    // C(pi-2)=C(pi)-P(pi)
    SumMin -= exp(Log);
    // P(pi-2)
    Log -= log((double)2 * p * (N - pi) * (N - pi - 1) / ((pi + 2) * (pi + 2) - J * J));
  }
  Lookup[N][abs(J)].Loghalf = (1) / (Sum - SumMin);
  Lookup[N][abs(J)].pihalf = piStart;
  Lookup[N][abs(J)].Sumhalf = (1 - SumMin) / (Sum - SumMin);
}

int PiLookup(int N, int NMax, int J)
{
  // System Variables
  double p = 0.125; // TODO: Change to prob array
  double Sum = 1, Log = 0;
  int pi;
  // Generate Saved Points if not already done
  if (N >= 3 * Nmax)
  {
    printf("Out of Array Bounds N\n");
    return -1;
  }
  if (J > N)
    printf("out of Array Bounds J\n");
  if (Lookup[N][J].pihalf < 0)
  {
    PiGenerate(N, NMax, J);
    // PiGenerate(N,J);
  }
  // Sampling Procedure
  double r = (double)rand() / RAND_MAX;
  if (r <= 0)
    return J;
  else if (r >= 1)
    return N;
  else if (J + 2 > N)
    return abs(J);
  else
  {
    Sum = Lookup[N][abs(J)].Sumhalf;
    Log = Lookup[N][abs(J)].Loghalf;
    pi = Lookup[N][abs(J)].pihalf;
    if (r > Sum)
    {
      while (r > Sum)
      {
        Log *= ((double)2 * p * (N - pi) * (N - pi - 1) / ((pi + 2) * (pi + 2) - J * J));
        Sum += Log;
        pi = pi + 2;
        // debug failsafe
        if (pi > N)
          printf("\npi>N");
      }
      return (pi);
    }
    else
    {
      while (r < Sum)
      {
        Sum -= Log;
        pi = pi - 2;
        Log /= ((double)2 * p * (N - pi) * (N - pi - 1) / ((pi + 2) * (pi + 2) - J * J));
        // debug failsafe
        if (pi < -2)
        {
          printf("\npi<0");
        }
      }
      return (pi + 2);
    }
  }
}

// Allocate lookup tables for the full local equilibrium pi distribution, along with the associated forward and reverse cumulative distributions
//Then assign values to the full distribution, using the central point calculated in PiGenerate
void GeneratePiDistributions(int N, int NMax, int J)
{
    piDistribution.size=NMax-abs(J)+1;
    piDistribution.array=malloc(piDistribution.size*sizeof(double));
    CumDist.size=NMax-abs(J)+1;
    CumDist.array=malloc(CumDist.size*sizeof(double));
    CumInv.size=NMax-abs(J)+1;
    CumInv.array=malloc(CumInv.size*sizeof(double));
    int pi;
    double Log, Sum, p=0.125;
    if (Lookup[N][abs(J)].pihalf<0){
        PiGenerate(N,NMax,J);
    }
    pi=Lookup[N][abs(J)].pihalf;
    Log=Lookup[N][abs(J)].Loghalf;
    Sum=0;
    while(pi<=NMax){
      if (pi>N)
        //debug failsafe
	    printf("\npi>N");
      piDistribution.array[pi-abs(J)]=Log;//assign pi distribution values
      Log*=((double)2*p*(N-pi)*(N-pi-1)/((pi+2)*(pi+2)-J*J));
      pi=pi+2;
    }
    pi=Lookup[N][abs(J)].pihalf;
    Log=Lookup[N][abs(J)].Loghalf;
    while(pi>abs(J)+1){
      if (pi<J)
        //debug failsafe
	    printf("\npi<J");
      pi=pi-2;
      Log/=((double)2*p*(N-pi)*(N-pi-1)/((pi+2)*(pi+2)-J*J));
      piDistribution.array[pi-abs(J)]=Log;//assign pi distribution values
    }
    CumDist.array[0]=piDistribution.array[0];
    CumInv.array[NMax-abs(J)]=piDistribution.array[NMax-abs(J)];///////////////////////////
    for (int i=abs(J)+2;i<=NMax;i+=2)
    {
        CumDist.array[i-abs(J)]=CumDist.array[i-abs(J)-2]+piDistribution.array[i-abs(J)];
        CumInv.array[NMax-i]=CumInv.array[NMax-i+2]+piDistribution.array[NMax-i];//////////////////
    }    
    //printf("%e\n",Sum);
}

void FreePiDistribution()
{
  free(piDistribution.array);
  free(CumDist.array);
  free(CumInv.array);
}

// Initialization Routine

void initSin()
{
  // Initialize GSL
  gsl_rng_env_setup();
  TYPE = gsl_rng_default;
  RANDOM = gsl_rng_alloc(TYPE);
  gsl_rng_set(RANDOM, Seed);
  // Distribute Particles
  for (int x = 0; x < dim; x++)
  {
    for (int v = 0; v < V; v++)
    {
      double lam = (NBarEqSin + amp * sin(2 * M_PI * x / dim)) * w[v];
      n[x][v] = poissonLog(lam);
    }
  }
  iterations = 0;
  if (LookupTable == 1)
  {
    Nmax = NBarEqSin;
    DestroyLookupTable(5 * Nmax);
  }
  GenerateLookupTable(5 * Nmax);
}

void initSOD()
{
  // Initialize GSL
  gsl_rng_env_setup();
  TYPE = gsl_rng_default;
  RANDOM = gsl_rng_alloc(TYPE);
  gsl_rng_set(RANDOM, Seed);
  for (int x = 0; x < dim; x++)
  {
    if (x < dim / 4. || x > 3. / 4. * dim)
    {
      for (int v = 0; v < V; v++)
      {
        n[x][v] = poissonLog(NBarl * w[v] * (1 + 3 * vel[v] * uG + (3 * vel[v] * vel[v] - 1) * (sqrt(1 + 3 * uG * uG) - 1)));
      }
    }
    else
    {
      for (int v = 0; v < V; v++)
      {
        n[x][v] = poissonLog(NBarr * w[v] * (1 + 3 * vel[v] * uG + (3 * vel[v] * vel[v] - 1) * (sqrt(1 + 3 * uG * uG) - 1)));
      }
    }
  }
  iterations = 0;
  Nmax = fmax(NBarl, NBarr);
  if (LookupTable == 1)
  {
    DestroyLookupTable(5 * Nmax);
  }
  GenerateLookupTable(5 * Nmax);
  iterations = 0;
}

// Iteration Routine

void iterate()
{
  for (int x = 0; x < dim; x++)
  {
    // Calculate total N (local)
    int N = 0;
    for (int v = 0; v < V; v++)
      N += n[x][v];
    // Calculate J (local)
    int J = n[x][2] - n[x][0], altJ;
    int NMax=(N%2==abs(J)%2)?(N):(N-1);
    // Sample pi
    int pi;
    if (J < 0)
    {
      altJ = -J;
      pi = PiLookup(N, NMax, altJ);
      // Use pi to distribute particles
      n[x][2] = (pi - altJ) / 2;
      n[x][1] = N - pi;
      n[x][0] = (pi + altJ) / 2;
    }
    else
    {
      pi = PiLookup(N, NMax, J);
      // Use pi to distribute particles
      n[x][0] = (pi - J) / 2;
      n[x][1] = N - pi;
      n[x][2] = (pi + J) / 2;
    }
  }
  // Streaming
  double tmp = n[0][0];
  for (int x = 1; x < dim; x++)
    n[x - 1][0] = n[x][0];
  n[dim - 1][0] = tmp;
  tmp = n[dim - 1][2];
  for (int x = dim - 2; x >= 0; x--)
    n[x + 1][2] = n[x][2];
  n[0][2] = tmp;
  iterations++;
}

void iterateUnder()
{
  for (int x = 0; x < dim; x++)
  {
    // Calculate total N (local)
    int N = 0;
    for (int v = 0; v < V; v++)
    {
      Nleft[v] = GSL(n[x][v], omega);
      N += Nleft[v];
      Nadd[v] = n[x][v] - Nleft[v];
    }
    // Calculate J (local)
    int J = Nleft[2] - Nleft[0], altJ;
    int NMax=(N%2==abs(J)%2)?(N):(N-1);
    // Sample pi
    int pi;
    if (J < 0)
    {
      altJ = -J;
      // pi=pidistsampling(N, altJ);
      pi = PiLookup(N, NMax, altJ);
      // Use pi to distribute particles
      n[x][2] = (pi - altJ) / 2 + Nadd[2];
      n[x][1] = N - pi + Nadd[1];
      n[x][0] = (pi + altJ) / 2 + Nadd[0];
    }
    else
    {
      // pi=pidistsampling(N,J);
      pi = PiLookup(N, NMax, J);
      // Use pi to distribute particles
      n[x][0] = (pi - J) / 2 + Nadd[0];
      n[x][1] = N - pi + Nadd[1];
      n[x][2] = (pi + J) / 2 + Nadd[2];
    }
  }
  // Streaming
  double tmp = n[0][0];
  for (int x = 1; x < dim; x++)
    n[x - 1][0] = n[x][0];
  n[dim - 1][0] = tmp;
  tmp = n[dim - 1][2];
  for (int x = dim - 2; x >= 0; x--)
    n[x + 1][2] = n[x][2];
  n[0][2] = tmp;
  iterations++;
}

//Mirror Operation
void OverFlip(int x){
  int pi, J, piPlus, piMinus, altJ;
  double piAvg, pistar, pMinus, r, rCum;
  int N=0;
  for (int v=0; v<V; v++)
      N+=n[x][v];
  pi=n[x][0]+n[x][2];
  int pitmp=pi;
  J=-n[x][0]+n[x][2];
  int NMax=(N%2==abs(J)%2)?(N):(N-1);
  GeneratePiDistributions(N,NMax,J);
  r=(double)rand()/RAND_MAX;
  if (pi==abs(J))
  {
      rCum=r*piDistribution.array[0];
  }
  else
  {
      rCum=CumDist.array[pi-abs(J)-2]+r*piDistribution.array[pi-abs(J)];
  }
  pi=NMax;
  while (rCum>CumInv.array[pi-abs(J)])
  {
      pi-=2;
      if (pi<abs(J))
      {
          printf("pi<J N=%i, J=%i, pi=%i,rCum=%e, r=%e, pitmp=%i, InvArrayMax=%e, ArrayMax=%e, iterations=%i\n",N,J,pi,rCum, r, pitmp, CumInv.array[0], CumDist.array[NMax-abs(J)], iterations);
    pi=abs(J);
    rCum=CumInv.array[pi-abs(J)]-1;
    //SkipBool=1;
      }
  }
  if (J<0){
      altJ=-J;
      n[x][2]= (pi-altJ)/2;
      n[x][1] = N-pi;
      n[x][0]=(pi+altJ)/2;
  }
  else{
      n[x][0]= (pi-J)/2;
      n[x][1] = N-pi;
      n[x][2]=(pi+J)/2; 
  }
  FreePiDistribution();
}

void iterateOver(){
  int pi, J, altJ, N;
for (int x=0; x<dim; x++){
  //Calculate total N (local)
  OverFlip(x);
  N=0; 
  J=0;
  pi=0;
  for (int v=0; v<V; v++){
   Nleft[v]=GSL(n[x][v],2.-omega);
   N+=Nleft[v];
   Nadd[v]=n[x][v]-Nleft[v];
  }
  //Calculate J (local)
  int J = Nleft[2]-Nleft[0], altJ;
  int NMax=(N%2==abs(J)%2)?(N):(N-1);
  //Sample pi
  int pi;
  if (J<0){
    altJ=-J;
    pi=PiLookup(N,NMax,altJ);
    //Use pi to distribute particles
    n[x][2]= (pi-altJ)/2+Nadd[2];
    n[x][1] = N-pi+Nadd[1];
    n[x][0]=(pi+altJ)/2+Nadd[0];
  }
  else{
    //pi=pidistsampling(N,J);
    pi=PiLookup(N,NMax,J);
    //Use pi to distribute particles
    n[x][0]= (pi-J)/2+Nadd[0];
    n[x][1] = N-pi+Nadd[1];
    n[x][2]=(pi+J)/2+Nadd[2];
  }
}
//Streaming
double tmp=n[0][0];
for (int x=1; x<dim; x++)
  n[x-1][0]=n[x][0];
n[dim-1][0]=tmp;
tmp=n[dim-1][2];
for (int x=dim-2; x>=0; x--)
  n[x+1][2]=n[x][2];
  n[0][2]=tmp;
iterations++;
}

// Gather Data for Graphing
void getdata()
{
  for (int x = 0; x < dim; x++)
  {
    NData[x] = 0;
    JData[x] = 0;
    PiData[x] = 0;
    for (int v = 0; v < V; v++)
      NData[x] += n[x][v];
    JData[x] = -n[x][0] + n[x][2];
    PiData[x] = n[x][0] + n[x][2];
  }
}

int main()
{
  int repeat = 50;
  int sstep = 0, cont = 0, done = 0;
  struct timespec
  {
    time_t s;
    long ns;
  } ts;
  ts.s = 0;
  ts.ns = 1000000;

  DefineGraphN_R("N", &NData[0], &DIM, NULL);
  DefineGraphN_R("J", &JData[0], &DIM, NULL);
  DefineGraphN_R("Pi", &PiData[0], &DIM, NULL);

  initSin();

  StartMenu("LG1D GUI", 1);
  DefineInt("Iterations", &iterations);
  DefineMod("dim", &DIM, dim + 1);
  DefineDouble("omega", &omega);

  StartMenu("Decaying Sound Wave", 0);
  DefineDouble("Average Density", &NBarEqSin);
  DefineDouble("Amplitude", &amp);
  DefineFunction("Init", initSin);
  EndMenu();

  StartMenu("SOD Shock Tube", 0);
  DefineDouble("Average Left Side Density", &NBarl);
  DefineDouble("Average Right Side Density", &NBarr);
  DefineFunction("Init", initSOD);
  EndMenu();

  DefineLong("sleep", &ts.ns);
  DefineGraph(curve2d_, "Graphs");
  DefineInt("repeat", &repeat);
  DefineBool("sstep", &sstep);
  DefineBool("cont", &cont);
  DefineBool("done", &done);
  EndMenu();

  while (!done)
  {
    Events(1);
    DrawGraphs();
    getdata();
    if (sstep || cont)
    {
      sstep = 0;
      for (int i = 0; i < repeat; i++)
      {
        if (omega > 1)
        {
          iterateOver();
        }
        else if (omega < 1)
        {
          iterateUnder();
        }
        else
        {
          iterate();
        }
      }
    }
    nanosleep(&ts, NULL);
  }
}
