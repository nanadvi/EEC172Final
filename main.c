// Simplelink includes
#include "simplelink.h"
//Driverlib includes
#include "hw_types.h"
#include "hw_ints.h"
#include "hw_memmap.h"
#include "hw_common_reg.h"
#include "interrupt.h"
#include "rom_map.h"
#include "hw_apps_rcm.h"
#include "prcm.h"
#include "rom.h"
#include "utils.h"
#include "gpio.h"
#include "utils.h"
#include "timer.h"
#include "systick.h"
#include "spi.h"
#include "uart.h"
#include <stdint.h>
#include <inttypes.h>
#include <string.h>
#include <math.h>
//Common interface includes
#include "uart_if.h"
#include "timer_if.h"
#include "pin_mux_config.h"
#include "gpio_if.h"
#include "common.h"
#include "uart_if.h"
// Adafruit includes
#include "Adafruit_GFX.h"
#include "Adafruit_SSD1351.h"
#include "glcdfont.h"
// draw functions includes
#include "test.h"

#define SPI_IF_BIT_RATE  1000000
#define TR_BUFF_SIZE 100
// Definitions for Simplelink
#define MAX_URI_SIZE 128
#define URI_SIZE MAX_URI_SIZE + 1
#define APPLICATION_NAME        "SSL"
#define APPLICATION_VERSION     "1.1.1.EEC.Winter2018"
#define SERVER_NAME                "a2mwr78sr5pnme.iot.us-east-1.amazonaws.com"
#define GOOGLE_DST_PORT             8443

#define SL_SSL_CA_CERT "/cert/rootCA.der"
#define SL_SSL_PRIVATE "/cert/private.der"
#define SL_SSL_CLIENT  "/cert/client.der"


//NEED TO UPDATE THIS FOR IT TO WORK!
#define DATE                1    /* Current Date */
#define MONTH               3     /* Month 1-12 */
#define YEAR                2018  /* Current year */
#define HOUR                10    /* Time - hours */
#define MINUTE              19    /* Time - minutes */
#define SECOND              0     /* Time - seconds */

#define POSTHEADER "POST /things/sailesh_cc3200Board/shadow HTTP/1.1\r\n"
#define GETHEADER "GET /things/sailesh_cc3200Board/shadow HTTP/1.1\r\n"
#define HOSTHEADER "Host: a2mwr78sr5pnme.iot.us-east-1.amazonaws.com\r\n"
#define CHEADER "Connection: Keep-Alive\r\n"
#define CTHEADER "Content-Type: application/json; charset=utf-8\r\n"
#define CLHEADER1 "Content-Length: "
#define CLHEADER2 "\r\n\r\n"

#define min(a, b) (((a) < (b)) ? (a) : (b))
#define max(a, b) (((a) > (b)) ? (a) : (b))

#define DATA1 "{\"state\": {\n\r\"desired\" : {\n\r\"color\" : \"green\"\r\n}}}\r\n\r\n"

#define BEGIN_JSON_STRING "{\"state\": {\n\r\"desired\" : {"
#define END_JSON_STRING "}}}\r\n\r\n"

// Application specific status/error codes
typedef enum{
    // Choosing -0x7D0 to avoid overlap w/ host-driver's error codes
    LAN_CONNECTION_FAILED = -0x7D0,
    INTERNET_CONNECTION_FAILED = LAN_CONNECTION_FAILED - 1,
    DEVICE_NOT_IN_STATION_MODE = INTERNET_CONNECTION_FAILED - 1,

    STATUS_CODE_MAX = -0xBB8
}e_AppStatusCodes;

typedef struct
{
   /* time */
   unsigned long tm_sec;
   unsigned long tm_min;
   unsigned long tm_hour;
   /* date */
   unsigned long tm_day;
   unsigned long tm_mon;
   unsigned long tm_year;
   unsigned long tm_week_day; //not required
   unsigned long tm_year_day; //not required
   unsigned long reserved[3];
}SlDateTime;

typedef struct PinSetting {
    unsigned long port;
    unsigned int pin;
} PinSetting;
static PinSetting gpioin = { .port = GPIOA0_BASE, .pin = 0x40 };
//*****************************************************************************
//                 GLOBAL VARIABLES -- Start
//*****************************************************************************
volatile unsigned long  g_ulStatus = 0;//SimpleLink Status
unsigned long  g_ulPingPacketsRecv = 0; //Number of Ping Packets received
unsigned long  g_ulGatewayIP = 0; //Network Gateway IP address
unsigned char  g_ucConnectionSSID[SSID_LEN_MAX+1]; //Connection SSID
unsigned char  g_ucConnectionBSSID[BSSID_LEN_MAX]; //Connection BSSID
signed char    *g_Host = SERVER_NAME;
SlDateTime g_time;
#if defined(ccs) || defined(gcc)
extern void (* const g_pfnVectors[])(void);
#endif
#if defined(ewarm)
extern uVectorEntry __vector_table;
#endif

volatile unsigned long time;
int interruptCounter;
int pulseCounter;
int deleteFlag;
char lastRead;
char prevRead, currRead;
char buffer[64];
char receiverBuffer[64];
unsigned long _time;
unsigned long _readTime;
unsigned long timeInterval[35] = {};
unsigned long timeOfInterrupt[35] = {};
unsigned int bitSequence[35] = {};
int receiverLineNumber;
int readIndex;
const int pedalSize = 20;
const int pedalWidth = 5;
int buttons[12][35] = {
                       {0,0,0,0,0,0,0,0,0,0,1,1,1,1,0,1,1,1,1,0,1,1,0,0,0,0,0,1,0,0,1,1,1,1,0}, // 0
                       {0,0,0,0,0,0,0,0,0,0,1,1,1,1,0,1,1,1,0,0,0,0,0,0,0,0,1,1,1,1,1,1,1,1,0}, // 1
                       {0,0,0,0,0,0,0,0,0,0,1,1,1,1,0,1,1,1,1,0,0,0,0,0,0,0,0,1,1,1,1,1,1,1,0}, // 2
                       {0,0,0,0,0,0,0,0,0,0,1,1,1,1,0,1,1,1,0,1,0,0,0,0,0,0,1,0,1,1,1,1,1,1,0} // 3
};
int isPlayerOne = 1;
char message[100];

static char json[1024];
char recvJSON[1460];
// Grid of the table
int board[WIDTH][HEIGHT] = {{0}};

typedef struct BoardConfig
{
    int ballX;
    int ballY;
    int angle;
    int velX;
    int velY;
    int p1X;
    int p2X;
    int p1Y;
    int p2Y;
}BoardConfig;

static BoardConfig state = { .ballX = WIDTH/2,
                             .ballY = HEIGHT/2,
                             .angle = 45,
                             .velX = 2,
                             .velY = 2,
                             .p1X = (WIDTH/2)-pedalSize,
                             .p2X = (WIDTH/2)-pedalSize,
                             .p1Y = 0,
                             .p2Y = HEIGHT-pedalWidth};
// Ball starts from the middle of the board

//*****************************************************************************
//                 GLOBAL VARIABLES -- End
//*****************************************************************************


//****************************************************************************
//                      LOCAL FUNCTION PROTOTYPES
//****************************************************************************
static long WlanConnect();
static int set_time();
static void BoardInit(void);
static long InitializeAppVariables();
static int tls_connect();
static int connectToAccessPoint();
static int http_post(int,char*);

//*****************************************************************************
//                      LOCAL FUNCTION DEFINITIONS
//*****************************************************************************

void TimerRefIntHandler(void)
{
    //
    // Clear the timer interrupt.
    //
    unsigned long ulInts;
    ulInts = TimerIntStatus(TIMERA0_BASE, true);
    TimerIntClear(TIMERA0_BASE, ulInts);
    _time++;
    _readTime++;
}

int compareTwoSequence(int sequence1[35], int sequence2[35]) {
    int i;
    for (i = 0; i < 35; i++) {
        if (sequence1[i] != sequence2[i])
            return 0;
    }
    return 1;
}

char compareBitPatterns() {
    int row;
    int col;
    for (row = 0; row < 4; row++) {
        if (compareTwoSequence(bitSequence, buttons[row])) {
            lastRead = row + '0';
            return row + '0';
        }
    }
    return lastRead;
}

static char* StateToCommand()
{
    // "{\"state\": {\n\r\"desired\" : {\n\r\"color\" : \"green\"\r\n}}}\r\n\r\n"
    char h1[48];
    char* tmp;
    strcpy(h1, "{\"state\": {\n\r\"desired\" : {\n\r\"ballX\" : ");
    sprintf(tmp, "%d", state.ballX);
    strcat(h1, tmp);
}

static void GPIOA2IntHandler(void)
{
    unsigned long ulStatus;
    ulStatus = MAP_GPIOIntStatus (gpioin.port, false);
    MAP_GPIOIntClear(gpioin.port, ulStatus);        // clear interrupts on GPIOA2
    time = _time;
    _time = 0;
    int _interrupt = interruptCounter;
    if(interruptCounter < 35)
    {
        bitSequence[interruptCounter] = decode(time);
        timeOfInterrupt[interruptCounter] = time;
        interruptCounter++;
    }
    if(interruptCounter == 35)
    {
        // GPIOIntDisable(gpioin.port, gpioin.pin);
        // Don't tick till we read and decode the bits
        TimerDisable(TIMERA0_BASE, TIMER_A);
        // Stop taking ticks too
        // interruptCounter = 0;
        // initializeArr();
        // GPIOIntEnable(gpioin.port, gpioin.pin);
    }
}

void timerInit()
{
    Timer_IF_Init(PRCM_TIMERA0, TIMERA0_BASE, TIMER_CFG_PERIODIC, TIMER_A, 255);
    Timer_IF_IntSetup(TIMERA0_BASE, TIMER_A, TimerRefIntHandler);
    TimerLoadSet(TIMERA0_BASE, TIMER_A, 10000);
    TimerEnable(TIMERA0_BASE, TIMER_A);
}

void initializeArr()
{
    int i;
    for(i = 0; i < 35; i++)
    {
        timeInterval[i] = 0;
        timeOfInterrupt[i] = 0;
        bitSequence[i] = 0;
    }
}

void initializeVariables()
{
    interruptCounter = 0;
    pulseCounter = 0;
    _time = 0;
    readIndex = 0;
    lastRead = ' ';
    currRead = ' ';
    receiverLineNumber = 64;
    memset(buffer, ' ', 64);
    memset(receiverBuffer, ' ', 64);
    int fPressed = 0;
}

void printBuffer()
{
    int i;
    for(i = 0; i < readIndex; i++)
    {
        Report("%c", buffer[i]);
        drawChar(6*i, 30, buffer[i], WHITE, BLACK, 0x01);
    }
    Report("\n\r");

}

int decode(unsigned long time){

    if(time > 0 && time < 10){
        return 0;
    }
    else if(time > 10 && time < 20){
        return 1;
    }
    else if(time > 1000)
    {
        interruptCounter = 0;
    }
    return 0;
}

void SPI_Init() {
    // Reset SPI

    MAP_SPIReset(GSPI_BASE);

    //Enables the transmit and/or receive FIFOs.

    //Base address is GSPI_BASE, SPI_TX_FIFO || SPI_RX_FIFO are the FIFOs to be enabled

    MAP_SPIFIFOEnable(GSPI_BASE, SPI_TX_FIFO || SPI_RX_FIFO);

    // Configure SPI interface

    MAP_SPIConfigSetExpClk(GSPI_BASE,MAP_PRCMPeripheralClockGet(PRCM_GSPI),

                     SPI_IF_BIT_RATE,SPI_MODE_MASTER,SPI_SUB_MODE_0,

                     (SPI_SW_CTRL_CS |

                     SPI_4PIN_MODE |

                     SPI_TURBO_OFF |

                     SPI_CS_ACTIVELOW |

                     SPI_WL_8));

    // Enable SPI for communication

    MAP_SPIEnable(GSPI_BASE);
}


//*****************************************************************************
// SimpleLink Asynchronous Event Handlers -- Start
//*****************************************************************************


//*****************************************************************************
//
//! \brief The Function Handles WLAN Events
//!
//! \param[in]  pWlanEvent - Pointer to WLAN Event Info
//!
//! \return None
//!
//*****************************************************************************
void SimpleLinkWlanEventHandler(SlWlanEvent_t *pWlanEvent) {
    if(!pWlanEvent) {
        return;
    }

    switch(pWlanEvent->Event) {
        case SL_WLAN_CONNECT_EVENT: {
            SET_STATUS_BIT(g_ulStatus, STATUS_BIT_CONNECTION);

            //
            // Information about the connected AP (like name, MAC etc) will be
            // available in 'slWlanConnectAsyncResponse_t'.
            // Applications can use it if required
            //
            //  slWlanConnectAsyncResponse_t *pEventData = NULL;
            // pEventData = &pWlanEvent->EventData.STAandP2PModeWlanConnected;
            //

            // Copy new connection SSID and BSSID to global parameters
            memcpy(g_ucConnectionSSID,pWlanEvent->EventData.
                   STAandP2PModeWlanConnected.ssid_name,
                   pWlanEvent->EventData.STAandP2PModeWlanConnected.ssid_len);
            memcpy(g_ucConnectionBSSID,
                   pWlanEvent->EventData.STAandP2PModeWlanConnected.bssid,
                   SL_BSSID_LENGTH);

            UART_PRINT("[WLAN EVENT] STA Connected to the AP: %s , "
                       "BSSID: %x:%x:%x:%x:%x:%x\n\r",
                       g_ucConnectionSSID,g_ucConnectionBSSID[0],
                       g_ucConnectionBSSID[1],g_ucConnectionBSSID[2],
                       g_ucConnectionBSSID[3],g_ucConnectionBSSID[4],
                       g_ucConnectionBSSID[5]);
        }
        break;

        case SL_WLAN_DISCONNECT_EVENT: {
            slWlanConnectAsyncResponse_t*  pEventData = NULL;

            CLR_STATUS_BIT(g_ulStatus, STATUS_BIT_CONNECTION);
            CLR_STATUS_BIT(g_ulStatus, STATUS_BIT_IP_AQUIRED);

            pEventData = &pWlanEvent->EventData.STAandP2PModeDisconnected;

            // If the user has initiated 'Disconnect' request,
            //'reason_code' is SL_USER_INITIATED_DISCONNECTION
            if(SL_USER_INITIATED_DISCONNECTION == pEventData->reason_code) {
                UART_PRINT("[WLAN EVENT]Device disconnected from the AP: %s,"
                    "BSSID: %x:%x:%x:%x:%x:%x on application's request \n\r",
                           g_ucConnectionSSID,g_ucConnectionBSSID[0],
                           g_ucConnectionBSSID[1],g_ucConnectionBSSID[2],
                           g_ucConnectionBSSID[3],g_ucConnectionBSSID[4],
                           g_ucConnectionBSSID[5]);
            }
            else {
                UART_PRINT("[WLAN ERROR]Device disconnected from the AP AP: %s, "
                           "BSSID: %x:%x:%x:%x:%x:%x on an ERROR..!! \n\r",
                           g_ucConnectionSSID,g_ucConnectionBSSID[0],
                           g_ucConnectionBSSID[1],g_ucConnectionBSSID[2],
                           g_ucConnectionBSSID[3],g_ucConnectionBSSID[4],
                           g_ucConnectionBSSID[5]);
            }
            memset(g_ucConnectionSSID,0,sizeof(g_ucConnectionSSID));
            memset(g_ucConnectionBSSID,0,sizeof(g_ucConnectionBSSID));
        }
        break;

        default: {
            UART_PRINT("[WLAN EVENT] Unexpected event [0x%x]\n\r",
                       pWlanEvent->Event);
        }
        break;
    }
}

//*****************************************************************************
//
//! \brief This function handles network events such as IP acquisition, IP
//!           leased, IP released etc.
//!
//! \param[in]  pNetAppEvent - Pointer to NetApp Event Info
//!
//! \return None
//!
//*****************************************************************************
void SimpleLinkNetAppEventHandler(SlNetAppEvent_t *pNetAppEvent) {
    if(!pNetAppEvent) {
        return;
    }

    switch(pNetAppEvent->Event) {
        case SL_NETAPP_IPV4_IPACQUIRED_EVENT: {
            SlIpV4AcquiredAsync_t *pEventData = NULL;

            SET_STATUS_BIT(g_ulStatus, STATUS_BIT_IP_AQUIRED);

            //Ip Acquired Event Data
            pEventData = &pNetAppEvent->EventData.ipAcquiredV4;

            //Gateway IP address
            g_ulGatewayIP = pEventData->gateway;

            UART_PRINT("[NETAPP EVENT] IP Acquired: IP=%d.%d.%d.%d , "
                       "Gateway=%d.%d.%d.%d\n\r",
            SL_IPV4_BYTE(pNetAppEvent->EventData.ipAcquiredV4.ip,3),
            SL_IPV4_BYTE(pNetAppEvent->EventData.ipAcquiredV4.ip,2),
            SL_IPV4_BYTE(pNetAppEvent->EventData.ipAcquiredV4.ip,1),
            SL_IPV4_BYTE(pNetAppEvent->EventData.ipAcquiredV4.ip,0),
            SL_IPV4_BYTE(pNetAppEvent->EventData.ipAcquiredV4.gateway,3),
            SL_IPV4_BYTE(pNetAppEvent->EventData.ipAcquiredV4.gateway,2),
            SL_IPV4_BYTE(pNetAppEvent->EventData.ipAcquiredV4.gateway,1),
            SL_IPV4_BYTE(pNetAppEvent->EventData.ipAcquiredV4.gateway,0));
        }
        break;

        default: {
            UART_PRINT("[NETAPP EVENT] Unexpected event [0x%x] \n\r",
                       pNetAppEvent->Event);
        }
        break;
    }
}


//*****************************************************************************
//
//! \brief This function handles HTTP server events
//!
//! \param[in]  pServerEvent - Contains the relevant event information
//! \param[in]    pServerResponse - Should be filled by the user with the
//!                                      relevant response information
//!
//! \return None
//!
//****************************************************************************
void SimpleLinkHttpServerCallback(SlHttpServerEvent_t *pHttpEvent, SlHttpServerResponse_t *pHttpResponse) {
    // Unused in this application
}

//*****************************************************************************
//
//! \brief This function handles General Events
//!
//! \param[in]     pDevEvent - Pointer to General Event Info
//!
//! \return None
//!
//*****************************************************************************
void SimpleLinkGeneralEventHandler(SlDeviceEvent_t *pDevEvent) {
    if(!pDevEvent) {
        return;
    }

    //
    // Most of the general errors are not FATAL are are to be handled
    // appropriately by the application
    //
    UART_PRINT("[GENERAL EVENT] - ID=[%d] Sender=[%d]\n\n",
               pDevEvent->EventData.deviceEvent.status,
               pDevEvent->EventData.deviceEvent.sender);
}


//*****************************************************************************
//
//! This function handles socket events indication
//!
//! \param[in]      pSock - Pointer to Socket Event Info
//!
//! \return None
//!
//*****************************************************************************
void SimpleLinkSockEventHandler(SlSockEvent_t *pSock) {
    if(!pSock) {
        return;
    }

    switch( pSock->Event ) {
        case SL_SOCKET_TX_FAILED_EVENT:
            switch( pSock->socketAsyncEvent.SockTxFailData.status) {
                case SL_ECLOSE: 
                    UART_PRINT("[SOCK ERROR] - close socket (%d) operation "
                                "failed to transmit all queued packets\n\n", 
                                    pSock->socketAsyncEvent.SockTxFailData.sd);
                    break;
                default: 
                    UART_PRINT("[SOCK ERROR] - TX FAILED  :  socket %d , reason "
                                "(%d) \n\n",
                                pSock->socketAsyncEvent.SockTxFailData.sd, pSock->socketAsyncEvent.SockTxFailData.status);
                  break;
            }
            break;

        default:
            UART_PRINT("[SOCK EVENT] - Unexpected Event [%x0x]\n\n",pSock->Event);
          break;
    }
}


//*****************************************************************************
// SimpleLink Asynchronous Event Handlers -- End
//*****************************************************************************


//*****************************************************************************
//
//! \brief This function initializes the application variables
//!
//! \param    0 on success else error code
//!
//! \return None
//!
//*****************************************************************************
static long InitializeAppVariables() {
    g_ulStatus = 0;
    g_ulGatewayIP = 0;
    g_Host = SERVER_NAME;
    memset(g_ucConnectionSSID,0,sizeof(g_ucConnectionSSID));
    memset(g_ucConnectionBSSID,0,sizeof(g_ucConnectionBSSID));
    return SUCCESS;
}


//*****************************************************************************
//! \brief This function puts the device in its default state. It:
//!           - Set the mode to STATION
//!           - Configures connection policy to Auto and AutoSmartConfig
//!           - Deletes all the stored profiles
//!           - Enables DHCP
//!           - Disables Scan policy
//!           - Sets Tx power to maximum
//!           - Sets power policy to normal
//!           - Unregister mDNS services
//!           - Remove all filters
//!
//! \param   none
//! \return  On success, zero is returned. On error, negative is returned
//*****************************************************************************
static long ConfigureSimpleLinkToDefaultState() {
    SlVersionFull   ver = {0};
    _WlanRxFilterOperationCommandBuff_t  RxFilterIdMask = {0};

    unsigned char ucVal = 1;
    unsigned char ucConfigOpt = 0;
    unsigned char ucConfigLen = 0;
    unsigned char ucPower = 0;

    long lRetVal = -1;
    long lMode = -1;

    lMode = sl_Start(0, 0, 0);
    ASSERT_ON_ERROR(lMode);

    // If the device is not in station-mode, try configuring it in station-mode 
    if (ROLE_STA != lMode) {
        if (ROLE_AP == lMode) {
            // If the device is in AP mode, we need to wait for this event 
            // before doing anything 
            while(!IS_IP_ACQUIRED(g_ulStatus)) {
                #ifndef SL_PLATFORM_MULTI_THREADED
                _SlNonOsMainLoopTask();
                #endif
            }
        }

        // Switch to STA role and restart 
        lRetVal = sl_WlanSetMode(ROLE_STA);
        ASSERT_ON_ERROR(lRetVal);

        lRetVal = sl_Stop(0xFF);
        ASSERT_ON_ERROR(lRetVal);

        lRetVal = sl_Start(0, 0, 0);
        ASSERT_ON_ERROR(lRetVal);

        // Check if the device is in station again 
        if (ROLE_STA != lRetVal) {
            // We don't want to proceed if the device is not coming up in STA-mode 
            return DEVICE_NOT_IN_STATION_MODE;
        }
    }
    
    // Get the device's version-information
    ucConfigOpt = SL_DEVICE_GENERAL_VERSION;
    ucConfigLen = sizeof(ver);
    lRetVal = sl_DevGet(SL_DEVICE_GENERAL_CONFIGURATION, &ucConfigOpt, 
                                &ucConfigLen, (unsigned char *)(&ver));
    ASSERT_ON_ERROR(lRetVal);
    
    UART_PRINT("Host Driver Version: %s\n\r",SL_DRIVER_VERSION);
    UART_PRINT("Build Version %d.%d.%d.%d.31.%d.%d.%d.%d.%d.%d.%d.%d\n\r",
    ver.NwpVersion[0],ver.NwpVersion[1],ver.NwpVersion[2],ver.NwpVersion[3],
    ver.ChipFwAndPhyVersion.FwVersion[0],ver.ChipFwAndPhyVersion.FwVersion[1],
    ver.ChipFwAndPhyVersion.FwVersion[2],ver.ChipFwAndPhyVersion.FwVersion[3],
    ver.ChipFwAndPhyVersion.PhyVersion[0],ver.ChipFwAndPhyVersion.PhyVersion[1],
    ver.ChipFwAndPhyVersion.PhyVersion[2],ver.ChipFwAndPhyVersion.PhyVersion[3]);

    // Set connection policy to Auto + SmartConfig 
    //      (Device's default connection policy)
    lRetVal = sl_WlanPolicySet(SL_POLICY_CONNECTION, 
                                SL_CONNECTION_POLICY(1, 0, 0, 0, 1), NULL, 0);
    ASSERT_ON_ERROR(lRetVal);

    // Remove all profiles
    lRetVal = sl_WlanProfileDel(0xFF);
    ASSERT_ON_ERROR(lRetVal);

    

    //
    // Device in station-mode. Disconnect previous connection if any
    // The function returns 0 if 'Disconnected done', negative number if already
    // disconnected Wait for 'disconnection' event if 0 is returned, Ignore 
    // other return-codes
    //
    lRetVal = sl_WlanDisconnect();
    if(0 == lRetVal) {
        // Wait
        while(IS_CONNECTED(g_ulStatus)) {
#ifndef SL_PLATFORM_MULTI_THREADED
              _SlNonOsMainLoopTask();
#endif
        }
    }

    // Enable DHCP client
    lRetVal = sl_NetCfgSet(SL_IPV4_STA_P2P_CL_DHCP_ENABLE,1,1,&ucVal);
    ASSERT_ON_ERROR(lRetVal);

    // Disable scan
    ucConfigOpt = SL_SCAN_POLICY(0);
    lRetVal = sl_WlanPolicySet(SL_POLICY_SCAN , ucConfigOpt, NULL, 0);
    ASSERT_ON_ERROR(lRetVal);

    // Set Tx power level for station mode
    // Number between 0-15, as dB offset from max power - 0 will set max power
    ucPower = 0;
    lRetVal = sl_WlanSet(SL_WLAN_CFG_GENERAL_PARAM_ID, 
            WLAN_GENERAL_PARAM_OPT_STA_TX_POWER, 1, (unsigned char *)&ucPower);
    ASSERT_ON_ERROR(lRetVal);

    // Set PM policy to normal
    lRetVal = sl_WlanPolicySet(SL_POLICY_PM , SL_NORMAL_POLICY, NULL, 0);
    ASSERT_ON_ERROR(lRetVal);

    // Unregister mDNS services
    lRetVal = sl_NetAppMDNSUnRegisterService(0, 0);
    ASSERT_ON_ERROR(lRetVal);

    // Remove  all 64 filters (8*8)
    memset(RxFilterIdMask.FilterIdMask, 0xFF, 8);
    lRetVal = sl_WlanRxFilterSet(SL_REMOVE_RX_FILTER, (_u8 *)&RxFilterIdMask,
                       sizeof(_WlanRxFilterOperationCommandBuff_t));
    ASSERT_ON_ERROR(lRetVal);

    lRetVal = sl_Stop(SL_STOP_TIMEOUT);
    ASSERT_ON_ERROR(lRetVal);

    InitializeAppVariables();
    
    return lRetVal; // Success
}

static void createMessage(char* b) {
    char header[100];
    strcpy(header, "{\"state\": {\n\r\"desired\" : {\n\r\"message\" : \"");
    strcat(header, b);
    strcat(header, "\"\r\n}}}\r\n\r\n");
    strcpy(message, header);

}
//*****************************************************************************
//
//! Board Initialization & Configuration
//!
//! \param  None
//!
//! \return None
//
//*****************************************************************************
static void BoardInit(void) {
    /* In case of TI-RTOS vector table is initialize by OS itself */
    #ifndef USE_TIRTOS
    //
    // Set vector table base
    //
    #if defined(ccs)
    MAP_IntVTableBaseSet((unsigned long)&g_pfnVectors[0]);
    #endif
    #if defined(ewarm)
    MAP_IntVTableBaseSet((unsigned long)&__vector_table);
    #endif
    #endif
    //
    // Enable Processor
    //
    MAP_IntMasterEnable();
    MAP_IntEnable(FAULT_SYSTICK);

    PRCMCC3200MCUInit();
}


//****************************************************************************
//
//! \brief Connecting to a WLAN Accesspoint
//!
//!  This function connects to the required AP (SSID_NAME) with Security
//!  parameters specified in te form of macros at the top of this file
//!
//! \param  None
//!
//! \return  0 on success else error code
//!
//! \warning    If the WLAN connection fails or we don't aquire an IP
//!            address, It will be stuck in this function forever.
//
//****************************************************************************
static long WlanConnect() {
    SlSecParams_t secParams = {0};
    long lRetVal = 0;

    secParams.Key = SECURITY_KEY;
    secParams.KeyLen = strlen(SECURITY_KEY);
    secParams.Type = SECURITY_TYPE;

    UART_PRINT("Attempting connection to access point: ");
    UART_PRINT(SSID_NAME);
    UART_PRINT("... ...");
    lRetVal = sl_WlanConnect(SSID_NAME, strlen(SSID_NAME), 0, &secParams, 0);
    ASSERT_ON_ERROR(lRetVal);

    UART_PRINT(" Connected!!!\n\r");


    // Wait for WLAN Event
    while((!IS_CONNECTED(g_ulStatus)) || (!IS_IP_ACQUIRED(g_ulStatus))) {
        // Toggle LEDs to Indicate Connection Progress
        _SlNonOsMainLoopTask();
        GPIO_IF_LedOff(MCU_IP_ALLOC_IND);
        MAP_UtilsDelay(800000);
        _SlNonOsMainLoopTask();
        GPIO_IF_LedOn(MCU_IP_ALLOC_IND);
        MAP_UtilsDelay(800000);
    }

    return SUCCESS;

}

//*****************************************************************************
//
//! This function updates the date and time of CC3200.
//!
//! \param None
//!
//! \return
//!     0 for success, negative otherwise
//!
//*****************************************************************************

static int set_time() {
    long retVal;

    g_time.tm_day = DATE;
    g_time.tm_mon = MONTH;
    g_time.tm_year = YEAR;
    g_time.tm_sec = HOUR;
    g_time.tm_hour = MINUTE;
    g_time.tm_min = SECOND;

    retVal = sl_DevSet(SL_DEVICE_GENERAL_CONFIGURATION,
                          SL_DEVICE_GENERAL_CONFIGURATION_DATE_TIME,
                          sizeof(SlDateTime),(unsigned char *)(&g_time));

    ASSERT_ON_ERROR(retVal);
    return SUCCESS;
}

static long ConnectToInternet()
{
    long lRetVal = -1;
    lRetVal = connectToAccessPoint();
    //Set time so that encryption can be used
    lRetVal = set_time();
    if(lRetVal < 0) {
        UART_PRINT("Unable to set time in the device");
        LOOP_FOREVER();
    }
    //Connect to the website with TLS encryption
    lRetVal = tls_connect();
    if(lRetVal < 0) {
        ERR_PRINT(lRetVal);
    }
    return lRetVal;
}

//*****************************************************************************
//
//! This function demonstrates how certificate can be used with SSL.
//! The procedure includes the following steps:
//! 1) connect to an open AP
//! 2) get the server name via a DNS request
//! 3) define all socket options and point to the CA certificate
//! 4) connect to the server via TCP
//!
//! \param None
//!
//! \return  0 on success else error code
//! \return  LED1 is turned solid in case of success
//!    LED2 is turned solid in case of failure
//!
//*****************************************************************************
static int tls_connect() {
    SlSockAddrIn_t    Addr;
    int    iAddrSize;
    unsigned char    ucMethod = SL_SO_SEC_METHOD_TLSV1_2;
    unsigned int uiIP,uiCipher = SL_SEC_MASK_TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA;
    long lRetVal = -1;
    int iSockID;

    lRetVal = sl_NetAppDnsGetHostByName(g_Host, strlen((const char *)g_Host),
                                    (unsigned long*)&uiIP, SL_AF_INET);

    if(lRetVal < 0) {
        return printErrConvenience("Device couldn't retrieve the host name \n\r", lRetVal);
    }

    Addr.sin_family = SL_AF_INET;
    Addr.sin_port = sl_Htons(GOOGLE_DST_PORT);
    Addr.sin_addr.s_addr = sl_Htonl(uiIP);
    iAddrSize = sizeof(SlSockAddrIn_t);
    //
    // opens a secure socket 
    //
    iSockID = sl_Socket(SL_AF_INET,SL_SOCK_STREAM, SL_SEC_SOCKET);
    if( iSockID < 0 ) {
        return printErrConvenience("Device unable to create secure socket \n\r", lRetVal);
    }
    //
    // configure the socket as TLS1.2
    //
    lRetVal = sl_SetSockOpt(iSockID, SL_SOL_SOCKET, SL_SO_SECMETHOD, &ucMethod,\
                               sizeof(ucMethod));
    if(lRetVal < 0) {
        return printErrConvenience("Device couldn't set socket options \n\r", lRetVal);
    }
    //
    //configure the socket as ECDHE RSA WITH AES256 CBC SHA
    //
    lRetVal = sl_SetSockOpt(iSockID, SL_SOL_SOCKET, SL_SO_SECURE_MASK, &uiCipher,\
                           sizeof(uiCipher));
    if(lRetVal < 0) {
        return printErrConvenience("Device couldn't set socket options \n\r", lRetVal);
    }

    //
    //configure the socket with CA certificate - for server verification
    //
    lRetVal = sl_SetSockOpt(iSockID, SL_SOL_SOCKET, \
                           SL_SO_SECURE_FILES_CA_FILE_NAME, \
                           SL_SSL_CA_CERT, \
                           strlen(SL_SSL_CA_CERT));
    if(lRetVal < 0) {
        return printErrConvenience("Device couldn't set socket options \n\r", lRetVal);
    }
    //configure the socket with Client Certificate - for server verification
    //
    lRetVal = sl_SetSockOpt(iSockID, SL_SOL_SOCKET, \
                SL_SO_SECURE_FILES_CERTIFICATE_FILE_NAME, \
                                    SL_SSL_CLIENT, \
                           strlen(SL_SSL_CLIENT));
    if(lRetVal < 0) {
        return printErrConvenience("Device couldn't set socket options \n\r", lRetVal);
    }

    //configure the socket with Private Key - for server verification
    //
    lRetVal = sl_SetSockOpt(iSockID, SL_SOL_SOCKET, \
            SL_SO_SECURE_FILES_PRIVATE_KEY_FILE_NAME, \
            SL_SSL_PRIVATE, \
                           strlen(SL_SSL_PRIVATE));

    if(lRetVal < 0) {
        return printErrConvenience("Device couldn't set socket options \n\r", lRetVal);
    }
    /* connect to the peer device - Google server */
    lRetVal = sl_Connect(iSockID, ( SlSockAddr_t *)&Addr, iAddrSize);

    if(lRetVal < 0) {
        UART_PRINT("Device couldn't connect to server:");
        UART_PRINT(SERVER_NAME);
        UART_PRINT("\n\r");
        return printErrConvenience("Device couldn't connect to server \n\r", lRetVal);
    }
    else {
        UART_PRINT("Device has connected to the website:");
        UART_PRINT(SERVER_NAME);
        UART_PRINT("\n\r");
    }
    GPIO_IF_LedOff(MCU_RED_LED_GPIO);
    GPIO_IF_LedOn(MCU_GREEN_LED_GPIO);
    return iSockID;
}

long printErrConvenience(char * msg, long retVal) {
    UART_PRINT(msg);
    GPIO_IF_LedOn(MCU_RED_LED_GPIO);
    return retVal;
}

int connectToAccessPoint() {
    long lRetVal = -1;
    GPIO_IF_LedConfigure(LED1|LED3);

    GPIO_IF_LedOff(MCU_RED_LED_GPIO);
    GPIO_IF_LedOff(MCU_GREEN_LED_GPIO);

    lRetVal = InitializeAppVariables();
    ASSERT_ON_ERROR(lRetVal);

    /*
     * Following function configure the device to default state by cleaning
     * the persistent settings stored in NVMEM (viz. connection profiles &
     * policies, power policy etc)
     * Applications may choose to skip this step if the developer is sure
     * that the device is in its default state at start of applicaton

     * Note that all profiles and persistent settings that were done on the
     * device will be lost
    */

    lRetVal = ConfigureSimpleLinkToDefaultState();
    if(lRetVal < 0) {
      if (DEVICE_NOT_IN_STATION_MODE == lRetVal)
          UART_PRINT("Failed to configure the device in its default state \n\r");

      return lRetVal;
    }

    UART_PRINT("Device is configured in default state \n\r");

    CLR_STATUS_BIT_ALL(g_ulStatus);

    ///
    // Assumption is that the device is configured in station mode already
    // and it is in its default state
    //
    lRetVal = sl_Start(0, 0, 0);
    if (lRetVal < 0 || ROLE_STA != lRetVal) {
        UART_PRINT("Failed to start the device \n\r");
        return lRetVal;
    }

    UART_PRINT("Device started as STATION \n\r");

    //
    //Connecting to WLAN AP
    //
    lRetVal = WlanConnect();
    if(lRetVal < 0) {
        UART_PRINT("Failed to establish connection w/ an AP \n\r");
        GPIO_IF_LedOn(MCU_RED_LED_GPIO);
        return lRetVal;
    }

    UART_PRINT("Connection established w/ AP and IP is aquired \n\r");
    return 0;
}

static int http_post(int iTLSSockID, char* m){
    char acSendBuff[512];
    char acRecvbuff[1460];
    char cCLLength[200];
    char* pcBufHeaders;
    int lRetVal = 0;

    pcBufHeaders = acSendBuff;
    strcpy(pcBufHeaders, POSTHEADER);
    pcBufHeaders += strlen(POSTHEADER);
    strcpy(pcBufHeaders, HOSTHEADER);
    pcBufHeaders += strlen(HOSTHEADER);
    strcpy(pcBufHeaders, CHEADER);
    pcBufHeaders += strlen(CHEADER);
    strcpy(pcBufHeaders, "\r\n\r\n");

//    char DATA[100];
//    memset(DATA, ' ', 100);

    int msgLength = (int)strlen(m);
//    strcpy(DATA, "{\"state\": {\n\r\"player:\" : {\n\r\"message\" : \"");
//    strncat(DATA, m, msgLength);
//    strcat(DATA, "\"\r\n}}}\r\n\r\n");

//    strcpy(DATA, message);
    msgLength = strlen(m);
    m[msgLength+1] = '\0';

    int dataLength = strlen(m);


    strcpy(pcBufHeaders, CTHEADER);
    pcBufHeaders += strlen(CTHEADER);
    strcpy(pcBufHeaders, CLHEADER1);

    pcBufHeaders += strlen(CLHEADER1);
    sprintf(cCLLength, "%d", dataLength);

    strcpy(pcBufHeaders, cCLLength);
    pcBufHeaders += strlen(cCLLength);
    strcpy(pcBufHeaders, CLHEADER2);
    pcBufHeaders += strlen(CLHEADER2);

    strcpy(pcBufHeaders, m);
    pcBufHeaders += strlen(m);

    int testDataLength = strlen(pcBufHeaders);

    // UART_PRINT(acSendBuff);


    //
    // Send the packet to the server */
    //
    lRetVal = sl_Send(iTLSSockID, acSendBuff, strlen(acSendBuff), 0);
    if(lRetVal < 0) {
        UART_PRINT("POST failed. Error Number: %i\n\r",lRetVal);
        delay(5);
        return http_post(iTLSSockID, m);
        // sl_Close(iTLSSockID);
        // GPIO_IF_LedOn(MCU_RED_LED_GPIO);
        // return lRetVal;
    }
    lRetVal = sl_Recv(iTLSSockID, &acRecvbuff[0], sizeof(acRecvbuff), 0);
    if(lRetVal < 0) {
        UART_PRINT("Received failed. Error Number: %i\n\r",lRetVal);
        delay(5);
        return http_post(iTLSSockID, m);
        // http_post(iTLSSockID, m);
        // sl_Close(iTLSSockID);
        // return lRetVal;
    }
    else {
        acRecvbuff[lRetVal+1] = '\0';
        // UART_PRINT(acRecvbuff);
        // UART_PRINT("\n\r\n\r");
    }

    return 0;
}

static int http_get(int iTLSSockID){
    char acSendBuff[512];
    char acRecvbuff[1460];
    char cCLLength[200];
    char* pcBufHeaders;
    int lRetVal = 0;

    pcBufHeaders = acSendBuff;
    strcpy(pcBufHeaders, GETHEADER);
    pcBufHeaders += strlen(GETHEADER);
    strcpy(pcBufHeaders, HOSTHEADER);
    pcBufHeaders += strlen(HOSTHEADER);
    strcpy(pcBufHeaders, CHEADER);
    pcBufHeaders += strlen(CHEADER);
    strcpy(pcBufHeaders, "\r\n\r\n");

    int testDataLength = strlen(pcBufHeaders);

    // UART_PRINT(acSendBuff);


    //
    // Send the packet to the server */
    //
    lRetVal = sl_Send(iTLSSockID, acSendBuff, strlen(acSendBuff), 0);
    if(lRetVal < 0) {
        UART_PRINT("GET failed. Error Number: %i\n\r",lRetVal);
        delay(5);
        return http_get(iTLSSockID);
        // http_get(iTLSSockID);
        // sl_Close(iTLSSockID);
        // GPIO_IF_LedOn(MCU_RED_LED_GPIO);
        // return lRetVal;
    }
    lRetVal = sl_Recv(iTLSSockID, &acRecvbuff[0], sizeof(acRecvbuff), 0);
    if(lRetVal < 0) {
        UART_PRINT("Received failed. Error Number: %i\n\r",lRetVal);
        delay(5);
        return http_get(iTLSSockID);
        // sl_Close(iTLSSockID);
        // GPIO_IF_LedOn(MCU_RED_LED_GPIO);
        // return lRetVal;
        // http_get(iTLSSockID);
    }
    else {
        acRecvbuff[lRetVal+1] = '\0';
        // UART_PRINT(acRecvbuff);
        strcpy(recvJSON, acRecvbuff);
        // UART_PRINT("\n\r\n\r");
    }

    return 0;
}

void updateJSON() {
    // "{\"state\": {\n\r\"desired\" : {\n\r\"color\" : \"green\"\r\n}}}\r\n\r\n"
    char tmp[48];

    strcpy(json, BEGIN_JSON_STRING);

    strcat(json, "\n\r\"ballX\": ");
    sprintf(tmp, "\"%03d\"", state.ballX);
    strcat(tmp, ",");
    strcat(json, tmp);

    strcat(json, "\n\r\"ballY\": ");
    sprintf(tmp, "\"%03d\"", state.ballY);
    strcat(tmp, ",");
    strcat(json, tmp);

    strcat(json, "\n\r\"angle\": ");
    sprintf(tmp, "\"%02d\"", state.angle);
    strcat(tmp, ",");
    strcat(json, tmp);

    strcat(json, "\n\r\"velX\": ");
    sprintf(tmp, "\"%1d\"", state.velX);
    strcat(tmp, ",");
    strcat(json, tmp);

    strcat(json, "\n\r\"velY\": ");
    sprintf(tmp, "\"%1d\"", state.velY);
    strcat(tmp, ",");
    strcat(json, tmp);

    strcat(json, "\n\r\"p1X\": ");
    sprintf(tmp, "\"%03d\"", state.p1X);
    strcat(tmp, ",");
    strcat(json, tmp);

    strcat(json, "\n\r\"p2X\": ");
    sprintf(tmp, "\"%03d\"", state.p2X);
    // strcat(tmp, ",");
    strcat(json, tmp);

    strcat(json, END_JSON_STRING);

}

void readJSON() {
    char tmp1;
    char tmp2[2];
    char tmp3[3];
    // update state ballX value

    tmp3[0] = recvJSON[239];
    tmp3[1] = recvJSON[240];
    tmp3[2] = recvJSON[241];

    int ballX = atoi(tmp3);
    state.ballX = ballX;

    // update ballY value
    tmp3[0] = recvJSON[253];
    tmp3[1] = recvJSON[254];
    tmp3[2] = recvJSON[255];

    int ballY = atoi(tmp3);
    state.ballY = ballY;

    // update angle value
    tmp2[0] = recvJSON[267];
    tmp2[1] = recvJSON[268];

    int angle = atoi(tmp2);
    state.angle = angle;

    // update velX value
    tmp1 = recvJSON[279];

    int velX = atoi(tmp1);
    if (velX == 1)
        state.velX *= -1;

    // update velY value
    tmp1 = recvJSON[290];

    int velY = atoi(tmp1);
    if (velY == 1)
        state.velY *= -1;

    // update p1X value
    tmp3[0] = recvJSON[300];
    tmp3[1] = recvJSON[301];
    tmp3[2] = recvJSON[302];

    int p1X = atoi(tmp3);
    state.p1X = p1X;

    // update p2X value
    tmp3[0] = recvJSON[312];
    tmp3[1] = recvJSON[313];
    tmp3[2] = recvJSON[314];

    int p2X = atoi(tmp3);
    state.p2X = p2X;

}

void displayBanner()
{
    Message("\t\t****************************************************\n\r");
    Message("\t\t\                      LAB 3                        \n\r");
    Message("\t\t****************************************************\n\r");
    Message("\n\n\n\r");
}

void GetMessage()
{
    // logic for matching the pattern and displaying character on OLED
    // 35 RISING HIGH INTERRUPTS
    if (interruptCounter == 35)
    {
        MAP_GPIOIntDisable(gpioin.port, gpioin.pin);
        currRead = compareBitPatterns();
        // replace above line with code to print to OLED
        // printf("%s\n", &currRead);
        _readTime = 0;
        interruptCounter = 0;
        initializeArr();
        MAP_GPIOIntEnable(gpioin.port, gpioin.pin);
        TimerEnable(TIMERA0_BASE, TIMER_A);
    }
}

void Draw(int e)
{
    // Erase
    if(e)
    {
        fillCircle(state.ballX, state.ballY, 5, BLACK);
        fillRect(state.p1X, state.p1Y, pedalSize, pedalWidth, BLACK);
        fillRect(state.p2X, state.p2Y, pedalSize, pedalWidth, BLACK);
    }
    else
    {
        fillCircle(state.ballX, state.ballY, 5, RED);
        fillRect(state.p1X, state.p1Y, pedalSize, pedalWidth, BLUE);
        fillRect(state.p2X, state.p2Y, pedalSize, pedalWidth, GREEN);
    }

}

static int isColliding()
{
    int retp1, retp2;
    int cirX = state.ballX;
    int cirY = state.ballY;
    int deltaXp1 = cirX - max(state.p1X, min(cirX, state.p1X+pedalSize));
    int deltaYp1 = cirY - max(state.p1Y, min(cirY, state.p1Y+pedalWidth));
    retp1 = (deltaXp1 * deltaXp1 + deltaYp1 * deltaYp1) < 25;
    int deltaXp2 = cirX - max(state.p2X, min(cirX, state.p2X+pedalSize));
    int deltaYp2 = cirY - max(state.p2Y, min(cirY, state.p2Y+pedalWidth));
    // printf("x: %d, y: %d\n", deltaXp2, deltaYp2);
    retp2 = (deltaXp2 * deltaXp2 + deltaYp2 * deltaYp2) < 25;
    return (retp1 || retp2);
}

void GameLogic()
{
    switch(isPlayerOne)
    {
        case 0:
            if(currRead == '1' && (state.p1X-8) > 0)
            {
                state.p1X -= 6;
            }
            else if(currRead == '3' && (state.p1X+8) < 128)
            {
                state.p1X += 6;
            }
            else
            {
            }
            if(state.p1X > 128)
            {
                state.p1X = 128-pedalSize;
                currRead = ' ';
            }
            if (state.p1X < 0)
            {
                state.p1X = pedalSize;
                currRead = ' ';
            }

            break;
        case 1:
            if(currRead == '1')
            {
                state.p2X -= 6;
                // currRead = ' ';
            }
            else if(currRead == '3')
            {
                state.p2X += 6;
                // currRead = ' ';
                // printf("%d\n", &state.p2X);
            }
            else
            {
            }
            if(state.p2X > 128)
            {
                state.p2X = 128-pedalSize;
                currRead = ' ';
            }
            if (state.p2X < 0)
            {
                state.p2X = 0;
                currRead = ' ';
            }
            break;
    }
    state.ballX += (cos(state.angle) * state.velX);
    state.ballY += (sin(state.angle) * state.velY);
    if(state.ballX - 5 < 0 || state.ballX + 5 > WIDTH)
    {
        state.velX *= -1;
    }
    if(state.ballY - 5 < 0 || state.ballY + 5 > HEIGHT)
    {
        state.ballX = 64;
        state.ballY = 64;
    }

    if(isColliding())
    {
        state.velY *= -1;
    }

    // printf("x: %d, y: %d\n", state.ballX, state.ballY);
    // currRead = ' ';

}

//*****************************************************************************
//
//! Main
//!
//! \param  none
//!
//! \return None
//!
//*****************************************************************************
void main()
{
    unsigned long ulStatus;
    long lRetVal;
    int snapTime = 0;
    //
    // Initialize board configuration
    //
    BoardInit();

    PinMuxConfig();

    InitTerm();
    ClearTerm();

    displayBanner();

    lRetVal = ConnectToInternet();

    // SPI config
    SPI_Init();

    // Adafruit init
    Adafruit_Init();

    fillScreen(BLACK);

    timerInit();
    // Register the interrupt handlers
    MAP_GPIOIntRegister(gpioin.port, GPIOA2IntHandler);
    //
    // Configure rising edge interrupts on PIN 61
    //
    MAP_GPIOIntTypeSet(gpioin.port, gpioin.pin, GPIO_RISING_EDGE);
    ulStatus = MAP_GPIOIntStatus (gpioin.port, false);
    MAP_GPIOIntClear(gpioin.port, ulStatus);            // clear interrupts on GPIOA2

    // Initialize all the global variables
    initializeVariables();
    initializeArr();

    MAP_GPIOIntEnable(gpioin.port, gpioin.pin);

    updateJSON();

    http_post(lRetVal, json);

    // setting timer value to 0
    TimerValueSet(TIMERA0_BASE, TIMER_A, 0);
    deleteFlag = 0;
    // Initialization
    // http_get(lRetVal);
    // http_post(lRetVal, DATA1);
    while (1) {
        GetMessage();
        snapTime++;
        // logic for matching the pattern and displaying character on OLED
        // 35 RISING HIGH INTERRUPTS
        Draw(1);
//        if(snapTime == 50)
//        {
//            http_get(lRetVal);
//            readJSON();
//            delay(2);
//            Draw(0);
//        }
        delay(2);
        GameLogic();
        Draw(0);
        delay(2);
//        if(snapTime == 50)
//        {
//            updateJSON();
//            http_post(lRetVal, json);
//            snapTime = 0;
//        }

    }
    sl_Stop(SL_STOP_TIMEOUT);
}
//*****************************************************************************
//
// Close the Doxygen group.
//! @}
//
//*****************************************************************************

