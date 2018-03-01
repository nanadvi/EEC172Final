
/* These functions are based on the Arduino test program at
*  https://github.com/adafruit/Adafruit-SSD1351-library/blob/master/examples/test/test.ino
*
*  You can use these high-level routines to implement your
*  test program.
*/

// TODO Configure SPI port and use these libraries to implement
// an OLED test program. See SPI example program.


#include "test.h"
#include "Adafruit_GFX.h"
#include "Adafruit_SSD1351.h"

float p = 3.1415926;

// Draw the Ball
void DrawBall(unsigned char x, unsigned char y, unsigned char radius, unsigned int color){
    fillCircle(x, y, radius, color);
}
//*****************************************************************************
//  function delays 3*ulCount cycles
void delay(unsigned long ulCount){
	int i;

  do{
    ulCount--;
		for (i=0; i< 65535; i++) ;
	}while(ulCount);
}

//*****************************************************************************
void drawAllFont() {
   unsigned char Font = 0;

   // clear the screen
   fillScreen(BLACK);

   // set initial coordinates
   char x = 0;
   char y = 0;

   while(1) {
       // make sure x and y don't go out of bounds
       if (x > 127 || x > 127) {
           break;
       }

       drawChar(x, y, Font, 0xFFF, 0x000, 1);

       // size of each font is 5x7
       x+=6;
       if (x > 120) {
           // reset x and y to next line
           x = 0;
           y += 8;
       }

       // print all fonts up to ascii value 256
       if (Font == 255) {
           break;
       }
       else {
           Font++;
       }
   }
}

//*****************************************************************************
void printHelloWorld() {
    // clear screen
    fillScreen(BLACK);

    drawChar(0, 64, 'H', 0xFFFF, 0x0000, 1);

    drawChar(6, 64, 'e', 0xFFFF, 0x0000, 1);

    drawChar(12, 64, 'l', 0xFFFF, 0x0000, 1);

    drawChar(18, 64, 'l', 0xFFFF, 0x0000, 1);

    drawChar(24, 64, 'o', 0xFFFF, 0x0000, 1);

    drawChar(30, 64, ' ', 0xFFFF, 0x0000, 1);

    drawChar(36, 64, 'w', 0xFFFF, 0x0000, 1);

    drawChar(42, 64, 'o', 0xFFFF, 0x0000, 1);

    drawChar(48, 64, 'r', 0xFFFF, 0x0000, 1);

    drawChar(54, 64, 'l', 0xFFFF, 0x0000, 1);

    drawChar(60, 64, 'd', 0xFFFF, 0x0000, 1);
}

//*****************************************************************************
void drawHorizontalLines() {
    // clear screen
    fillScreen(BLACK);

    int y;
    for (y = 0; y < 16; y++) {
        drawFastHLine(0, y, width()-1, BLACK);

        drawFastHLine(0, y + 16, width()-1, BLUE);

        drawFastHLine(0, y + 32, width()-1, GREEN);

        drawFastHLine(0, y + 48, width()-1, CYAN);

        drawFastHLine(0, y + 64, width()-1, RED);

        drawFastHLine(0, y + 80, width()-1, MAGENTA);

        drawFastHLine(0, y + 96, width()-1, YELLOW);

        drawFastHLine(0, y + 112, width()-1, WHITE);
    }
}

//*****************************************************************************
void drawVerticalLines() {
    //clear screen

    int x;
    for (x = 0; x < 16; x++) {
        drawFastVLine(x, 0, height()-1, BLACK);

        drawFastVLine(16+x, 0, height()-1, BLUE);

        drawFastVLine(32+x, 0, height()-1, GREEN);

        drawFastVLine(48+x, 0, height()-1, CYAN);

        drawFastVLine(64+x, 0, height()-1, RED);

        drawFastVLine(80+x, 0, height()-1, MAGENTA);

        drawFastVLine(96+x, 0, height()-1, YELLOW);

        drawFastVLine(112+x, 0, height()-1, WHITE);
    }
}

//*****************************************************************************
void testfastlines(unsigned int color1, unsigned int color2) {
	unsigned int x;
	unsigned int y;

   fillScreen(BLACK);
   for (y=0; y < height()-1; y+=8) {
     drawFastHLine(0, y, width()-1, color1);
   }
	 delay(100);
   for (x=0; x < width()-1; x+=8) {
     drawFastVLine(x, 0, height()-1, color2);
   }
	 delay(100);
}

//*****************************************************************************

void testdrawrects(unsigned int color) {
	unsigned int x;

 fillScreen(BLACK);
 for (x=0; x < height()-1; x+=6) {
   drawRect((width()-1)/2 -x/2, (height()-1)/2 -x/2 , x, x, color);
	 delay(10);
 }
}

//*****************************************************************************

void testfillrects(unsigned int color1, unsigned int color2) {

	unsigned char x;

 fillScreen(BLACK);
 for (x=height()-1; x > 6; x-=6) {
   fillRect((width()-1)/2 -x/2, (height()-1)/2 -x/2 , x, x, color1);
   drawRect((width()-1)/2 -x/2, (height()-1)/2 -x/2 , x, x, color2);
	 delay(10);
 }
}

//*****************************************************************************

void testfillcircles(unsigned char radius, unsigned int color) {
	unsigned char x;
	unsigned char y;

  for (x=radius; x < width()-1; x+=radius*2) {
    for (y=radius; y < height()-1; y+=radius*2) {
      fillCircle(x, y, radius, color);
			delay(10);
    }
  }
}

//*****************************************************************************

void testdrawcircles(unsigned char radius, unsigned int color) {
	unsigned char x;
	unsigned char y;

  for (x=0; x < width()-1+radius; x+=radius*2) {
    for (y=0; y < height()-1+radius; y+=radius*2) {
      drawCircle(x, y, radius, color);
			delay(10);
    }
  }
}

//*****************************************************************************

void testtriangles() {
  int color = 0xF800;
  int t;
  int w = width()/2;
  int x = height()-1;
  int y = 0;
  int z = width()-1;

  fillScreen(BLACK);
  for(t = 0 ; t <= 15; t+=1) {
    drawTriangle(w, y, y, x, z, x, color);
    x-=4;
    y+=4;
    z-=4;
    color+=100;
		delay(10);
  }
}

//*****************************************************************************

void testroundrects() {
  int color = 100;

	int i;
  int x = 0;
  int y = 0;
  int w = width();
  int h = height();

  fillScreen(BLACK);

  for(i = 0 ; i <= 24; i++) {
    drawRoundRect(x, y, w, h, 5, color);
    x+=2;
    y+=3;
    w-=4;
    h-=6;
    color+=1100;
  }
}

//*****************************************************************************
void testlines(unsigned int color) {
	unsigned int x;
	unsigned int y;

   fillScreen(BLACK);
   for (x=0; x < width()-1; x+=6) {
     drawLine(0, 0, x, height()-1, color);
   }
	 delay(10);
   for (y=0; y < height()-1; y+=6) {
     drawLine(0, 0, width()-1, y, color);
   }
	 delay(100);

   fillScreen(BLACK);
   for (x=0; x < width()-1; x+=6) {
     drawLine(width()-1, 0, x, height()-1, color);
   }
	 delay(100);
   for (y=0; y < height()-1; y+=6) {
     drawLine(width()-1, 0, 0, y, color);
   }
	 delay(100);

   fillScreen(BLACK);
   for (x=0; x < width()-1; x+=6) {
     drawLine(0, height()-1, x, 0, color);
   }
	 delay(100);
   for (y=0; y < height()-1; y+=6) {
     drawLine(0, height()-1, width()-1, y, color);
   }
	 delay(100);

   fillScreen(BLACK);
   for (x=0; x < width()-1; x+=6) {
     drawLine(width()-1, height()-1, x, 0, color);
   }
	 delay(100);
   for (y=0; y < height()-1; y+=6) {
     drawLine(width()-1, height()-1, 0, y, color);
   }
	 delay(100);

}

//*****************************************************************************

void lcdTestPattern(void)
{
  unsigned int i,j;
  goTo(0, 0);

  for(i=0;i<128;i++)
  {
    for(j=0;j<128;j++)
    {
      if(i<16){writeData(RED>>8); writeData((unsigned char) RED);}
      else if(i<32) {writeData(YELLOW>>8);writeData((unsigned char) YELLOW);}
      else if(i<48){writeData(GREEN>>8);writeData((unsigned char) GREEN);}
      else if(i<64){writeData(CYAN>>8);writeData((unsigned char) CYAN);}
      else if(i<80){writeData(BLUE>>8);writeData((unsigned char) BLUE);}
      else if(i<96){writeData(MAGENTA>>8);writeData((unsigned char) MAGENTA);}
      else if(i<112){writeData(BLACK>>8);writeData((unsigned char) BLACK);}
      else {writeData(WHITE>>8); writeData((unsigned char) WHITE);}
    }
  }
}
/**************************************************************************/
void lcdTestPattern2(void)
{
  unsigned int i,j;
  goTo(0, 0);

  for(i=0;i<128;i++)
  {
    for(j=0;j<128;j++)
    {
      if(j<16){writeData(RED>>8); writeData((unsigned char) RED);}
      else if(j<32) {writeData(YELLOW>>8);writeData((unsigned char) YELLOW);}
      else if(j<48){writeData(GREEN>>8);writeData((unsigned char) GREEN);}
      else if(j<64){writeData(CYAN>>8);writeData((unsigned char) CYAN);}
      else if(j<80){writeData(BLUE>>8);writeData((unsigned char) BLUE);}
      else if(j<96){writeData(MAGENTA>>8);writeData((unsigned char) MAGENTA);}
      else if(j<112){writeData(BLACK>>8);writeData((unsigned char) BLACK);}
      else {writeData(WHITE>>8);writeData((unsigned char) WHITE);}
    }
  }
}

/**************************************************************************/

