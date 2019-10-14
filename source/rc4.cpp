// rc4.cpp - implementation of the RC4 cipher

#include <stdio.h>

#include <iostream>
#include <string>
#include <sstream>

#include <time.h>

#if (defined _MSC_VER) || (defined __BORLANDC__)
  #include <io.h>
  #include <fcntl.h>
#endif

#ifdef __GNUC__
  #define __int64 long long
#endif

using namespace std;

class TRC4
{
  private:
    int sx, sy, sm[256]; // state
  public:
    TRC4(unsigned char* key, int length);
    unsigned char GetByte();
    void Crypt(unsigned char* data, int length);
};

TRC4::TRC4(unsigned char* key, int length)
{
    int i, j, k, a;
    sx = 0; sy = 0;
    for( i = 0; i < 256; i++ )
        sm[i] = i;
    j = k = 0;
    for( i = 0; i < 256; i++ )
    {
        a = sm[i];
        j = (unsigned char)(j + a + key[k]);
        sm[i] = sm[j]; sm[j] = a;
        if( ++k >= length ) k = 0;
    }
}


void TRC4::Crypt(unsigned char* data, int length)
{ 
  int i, a, b;
  for(i = 0; i<length; i++)
  {
    sx = (unsigned char)(sx+1); a = sm[sx];
    sy = (unsigned char)(sy+a);
    sm[sx] = b = sm[sy];
    sm[sy] = a;
    data[i] ^= sm[(unsigned char) ( a + b )]; // XOR
  }
}

unsigned char TRC4::GetByte()
{
  int a, b;
  sx = (unsigned char)(sx+1); a = sm[sx];
  sy = (unsigned char)(sy+a);
  sm[sx] = b = sm[sy];
  sm[sy] = a;
  return sm[(unsigned char) ( a + b )];
}

string KeyToStr(unsigned char* key)
{
  int i;
  char sss[128];
  string res;
  for(i=0; i<16; i++)
  {
    sprintf(sss, "%02x", key[i]);
    res = res + sss;
  }
  return res;
}


// ==========================

void PrintHelp()
{
  printf("RC4 generator. Writes the cipher's output into the stdout.\n");
  printf("Program usage:\n");
  printf("  rc4 [-k key] -n num -q\n");
  printf("    -k - specifies 128-bit key for the cipher as a hexadecimal number.\n");
  printf("      The prefix 0x is optional. If the parameter is omitted then\n");
  printf("      random generated key is used. The key is printed to stderr by default.\n");
  printf("    -n - specifies the number of bits to produce.\n");
  printf("    -q - quiet mode. Do not print the key to stderr.\n");
  printf("    -? - print this screen.\n");
  printf("Samples:\n");
  printf("  rc4 -k 0x0123456789abcdeffedcba9876543210 -n 536870912 -q\n");
  printf("  rc4 -k fedcba98765432100123456789abcdef -n 1073741824 >data.bin\n");
  printf("  rc4 -n 34359738368\n");
}

void Quit()
{
  PrintHelp();
  exit(1);
}

int main(int argc, char* argv[])
{
#ifdef _MSC_VER
  _setmode(_fileno(stdout), _O_BINARY);
#endif
#ifdef __BORLANDC__
   setmode(_fileno(stdout), O_BINARY);
#endif

  char digits1[] = "0123456789abcdef";
  char digits2[] = "ABCDEF";
  char back[256];
  memset(back, 100, 256);
  int i, j;
  for(i=0; i<16; i++) back[digits1[i]]=i;
  for(i=0; i<6; i++) back[digits2[i]]=i+10;

// parse commandline parameters
  __int64 nn=-1;
  char kk[16];
  bool qq = false;
  bool randomkey = true;

  for(i=1; i<argc; i++)
  {
    string arg = argv[i];
    bool onemore = argc>i+1;
    if(onemore)
    {
      if(arg=="-k")
      {
        i++;
        arg = argv[i];
        if((arg.length()>2)&&(arg.substr(0,2)=="0x"))
          arg = arg.substr(2);
        if(arg.length()>32)
        {
          printf("ERROR: The length of the key must not exceed 128-bit length.\n");
          Quit();
        }
        memset(kk,0,16);
        for(j=0; j<arg.length(); j++)
        {
          char c = back[arg[j]];
          if(c==100)
          {
            printf("ERROR: The entered key is not a hexadecimal value.\n");
            Quit();
          }
          kk[j/2] |= c << (4*(1-(j%2)));
        }
        randomkey = false;
      } else
      if(arg=="-n")
      {
        i++;
        istringstream is(argv[i]);
        is >> nn;
        if(is.fail()) Quit();
      } else Quit();
    } else
    {
      if(arg=="-q") qq = true;
      else Quit();
    }
  }
  
  if(nn<1)
  {
    printf("ERROR: You shoud enter a positive -n parameter.\n");
    Quit();
  }

  if(randomkey)
  {
    srand( (unsigned)time( NULL ) );
    for(i=0; i<16; i++)
      kk[i] = rand()&0xff;
  }

  TRC4 rc4((unsigned char*)kk, 16);

  if(!qq)
    fprintf(stderr,"Key used: 0x%s\n",KeyToStr((unsigned char*)kk).c_str());

  __int64 k,n;
  n = (nn+7)/8;

  for(k=0; k<n; k++)
    putchar((char) rc4.GetByte());

  return 0;
}
