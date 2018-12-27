/*
 * MODBUS协议
 * 
 * 
 * 介绍：
 * 此modbus上位机 协议类 具有较强的通用性
 * 本协议类最主要的思想是 把所有向下位机发送的指令 先存放在缓冲区中（命名为管道）
 * 再将管道中的指令逐个发送出去。
 * 管道遵守FIFO的模式。管道中所存放指令的个数 在全局变量中定义。
 * 管道内主要分为两部分：1，定时循环发送指令。2，一次性发送指令。
 * 定时循环发送指令:周期性间隔时间发送指令，一般针对“输入寄存器”或“输入线圈”等实时更新的变量。
 * 这两部分的长度由用户所添加指令个数决定（所以自由性强）。
 * 指令的最大发送次数，及管道中最大存放指令的个数在常量定义中 可进行设定。
 * 
 * 使用说明：
 * 1，首先对所定义的寄存器或线圈进行分组定义，并定义首地址。
 * 2，在MBDataTable数组中添加寄存器或线圈所对应的地址。 注意 寄存器：ob = new UInt16()。线圈：ob = new byte()。
 * 3，对所定义的地址 用属性进行定义 以方便在类外进行访问及了解所对应地址的含义。
 * 4，GetAddressValueLength函数中 对使用说明的"第一步"分组 的元素个数进行指定。
 * 5，在主程序中调用MBConfig进行协议初始化（初始化内容参考函数）。
 * 6，在串口中断函数中调用MBDataReceive()。
 * 7，定时器调用MBRefresh()。（10ms以下）
 *    指令发送间隔时间等于实时器乘以10。 例：定时器5ms调用一次  指令发送间隔为50ms。
 * 8，在主程序初始化中添加固定实时发送的指令操作 用MBAddRepeatCmd函数。
 * 9，在主程序运行过程中 根据需要添加 单个的指令操作(非固定重复发送的指令)用MBAddCmd函数。
 * 
 * 
 * 
 * 
 * 
 * 
 * 
*/

using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;
using System.IO.Ports;

namespace ModBus
{

    public class ModbusProtocol
    {
        #region 所用结构体
        /// <summary>
        /// 地址对应表元素单元
        /// </summary>
        public struct OPTable
        {
            public volatile int addr;
            public volatile byte type;
            public volatile object ob;
        };
        /// <summary>
        /// 当前的指令
        /// </summary>
        public struct MBCmd
        {
            /// <summary>
            /// 指令首地址
            /// </summary>
            public volatile int addr;
            /// <summary>
            /// 功能码
            /// </summary>
            public volatile int func;
            /// <summary>
            /// 所操作的寄存器或线圈的个数
            /// </summary>
            public volatile int len;
            /// <summary>
            /// 返回码的状态， 0：无返回，1：正确返回
            /// </summary>
            public volatile int res;
        };
        /// <summary>
        /// 当前操作的指令管道
        /// </summary>
        public struct MBSci
        {
            /// <summary>
            /// 指令结构体
            /// </summary>
            public volatile MBCmd[] cmd;
            /// <summary>
            /// 当前索引
            /// </summary>
            public volatile int index;
            /// <summary>
            /// 当前功能码执行的次数
            /// </summary>
            public volatile int count;
            /// <summary>
            /// 最大发送次数
            /// </summary>
            public volatile int maxRepeatCount;
            /// <summary>
            /// 实时读取的指令各数(无限间隔时间读取)
            /// </summary>
            public volatile int rtCount;
        };
        #endregion

        #region 常量定义

        /// <summary>
        /// 读线圈寄存器
        /// </summary>
        public const byte MB_READ_COILS = 0x01;
        /// <summary>
        /// 读离散输入寄存器
        /// </summary>
        public const byte MB_READ_DISCRETE = 0x02;
        /// <summary>
        /// 读保持寄存器
        /// </summary>
        public const byte MB_READ_HOLD_REG = 0x03;
        /// <summary>
        /// 读输入寄存器
        /// </summary>
        public const byte MB_READ_INPUT_REG = 0x04;
        /// <summary>
        /// 写单个线圈
        /// </summary>
        public const byte MB_WRITE_SINGLE_COIL = 0x05;
        /// <summary>
        /// 写单寄存器
        /// </summary>
        public const byte MB_WRITE_SINGLE_REG = 0x06;
        /// <summary>
        /// 写多线圈
        /// </summary>
        public const byte MB_WRITE_MULTIPLE_COILS = 0x0f;
        /// <summary>
        /// 写多寄存器
        /// </summary>
        public const byte MB_WRITE_MULTIPLE_REGS = 0x10;

        /// <summary>
        /// 最大数据长度
        /// </summary>
        private const int MB_MAX_LENGTH = 120;
        /// <summary>
        /// 指令管道最大存放的指令各数
        /// </summary>
        private const int MB_SCI_MAX_COUNT = 15;
        /// <summary>
        /// 指令最多发送次数
        /// </summary>
        private const int MB_MAX_REPEAT_COUNT = 3;

        #endregion

        #region 全局变量
        /// <summary>
        /// 调度器锁 true:加锁  false:解锁
        /// </summary>
        private static volatile bool sciLock = false;
        private static volatile byte[] buff = new byte[MB_MAX_LENGTH];      //接收缓冲器
        private static volatile int buffLen = 0;
        private static volatile byte[] rBuff = null;                  //正确接收缓冲器
        private static volatile byte[] wBuff = null;                     //正确发送缓冲器
        public static MBSci gMBSci = new MBSci() { cmd = new MBCmd[MB_SCI_MAX_COUNT], index = 0, maxRepeatCount = MB_MAX_REPEAT_COUNT, rtCount = 0, count = 0 };
        private static SerialPort comm = null;
        private static int mbRefreshTime = 0;
        #endregion

        #region MODBUS 地址对应表

        //modbus寄存器和线圈分组 首地址定义
        public const int D_DIO = 0x0000;
        public const int D_BASE = 0x0014;
        public const int D_RANGE = 0x0018;
        public const int D_PWM = 0x001A;
        public const int D_PID = 0x001E;

        /// <summary>
        /// 变量所对应的地址 在此位置
        /// 寄存器：ob = new UInt16()。线圈：ob = new byte()
        /// </summary>
        public static volatile OPTable[] MBDataTable =
        {
            new OPTable(){addr = D_DIO,         type = MB_READ_INPUT_REG,      ob = new UInt16()},      //0
            new OPTable(){addr = D_DIO + 1,     type = MB_READ_INPUT_REG,      ob = new UInt16()},
            new OPTable(){addr = D_DIO + 2,     type = MB_READ_INPUT_REG,      ob = new UInt16()},
            new OPTable(){addr = D_DIO + 3,     type = MB_READ_INPUT_REG,      ob = new UInt16()},
            new OPTable(){addr = D_DIO + 4,     type = MB_READ_INPUT_REG,      ob = new Int16()},
            new OPTable(){addr = D_DIO + 5,     type = MB_READ_INPUT_REG,      ob = new Int16()},

            new OPTable(){addr = D_BASE,        type = MB_READ_HOLD_REG,      ob = new Int16()},        //6
            new OPTable(){addr = D_BASE + 1,    type = MB_READ_HOLD_REG,      ob = new Int16()},
            new OPTable(){addr = D_BASE + 2,    type = MB_READ_HOLD_REG,      ob = new Int16()},
            new OPTable(){addr = D_BASE + 3,    type = MB_READ_HOLD_REG,      ob = new Int16()},

            new OPTable(){addr = D_RANGE,       type = MB_READ_HOLD_REG,      ob = new Int16()},        //10
            new OPTable(){addr = D_RANGE + 1,   type = MB_READ_HOLD_REG,      ob = new Int16()},

            new OPTable(){addr = D_PWM,         type = MB_READ_HOLD_REG,      ob = new Int16()},        //12
            new OPTable(){addr = D_PWM + 1,     type = MB_READ_HOLD_REG,      ob = new Int16()},
            new OPTable(){addr = D_PWM + 2,     type = MB_READ_HOLD_REG,      ob = new Int16()},
            new OPTable(){addr = D_PWM + 3,     type = MB_READ_HOLD_REG,      ob = new Int16()},

            new OPTable(){addr = D_PID,         type = MB_READ_HOLD_REG,      ob = new UInt16()},        //16
            new OPTable(){addr = D_PID + 1,     type = MB_READ_HOLD_REG,      ob = new UInt16()},
            new OPTable(){addr = D_PID + 2,     type = MB_READ_HOLD_REG,      ob = new UInt16()},
            new OPTable(){addr = D_PID + 3,     type = MB_READ_HOLD_REG,      ob = new UInt16()},
            new OPTable(){addr = D_PID + 4,     type = MB_READ_HOLD_REG,      ob = new UInt16()},
            new OPTable(){addr = D_PID + 5,     type = MB_READ_HOLD_REG,      ob = new UInt16()},

        };
        public static UInt16 gDioX { get { return Convert.ToUInt16(MBDataTable[0].ob); } set { MBDataTable[0].ob = value; } }
        public static UInt16 gDioY { get { return Convert.ToUInt16(MBDataTable[1].ob); } set { MBDataTable[1].ob = value; } }
        public static UInt16 gDioZ { get { return Convert.ToUInt16(MBDataTable[2].ob); } set { MBDataTable[2].ob = value; } }
        public static UInt16 gDioD { get { return Convert.ToUInt16(MBDataTable[3].ob); } set { MBDataTable[3].ob = value; } }
        public static Int16 gDioXx { get { return (Int16)Convert.ToInt32(MBDataTable[4].ob); } set { MBDataTable[4].ob = value; } }
        public static Int16 gDioXy { get { return (Int16)Convert.ToInt32(MBDataTable[5].ob); } set { MBDataTable[5].ob = value; } }

        public static Int16 gBaseF1 { get { return (Int16)Convert.ToInt32(MBDataTable[6].ob); } set { MBDataTable[6].ob = value; } }
        public static Int16 gBaseF2 { get { return (Int16)Convert.ToInt32(MBDataTable[7].ob); } set { MBDataTable[7].ob = value; } }
        public static Int16 gBaseF3 { get { return (Int16)Convert.ToInt32(MBDataTable[8].ob); } set { MBDataTable[8].ob = value; } }
        public static Int16 gBaseF4 { get { return (Int16)Convert.ToInt32(MBDataTable[9].ob); } set { MBDataTable[9].ob = value; } }

        public static Int16 gRangeMax { get { return (Int16)Convert.ToInt32(MBDataTable[10].ob); } set { MBDataTable[10].ob = value; } }
        public static Int16 gRangeMin { get { return (Int16)Convert.ToInt32(MBDataTable[11].ob); } set { MBDataTable[11].ob = value; } }

        public static Int16 gPwmF1 { get { return (Int16)Convert.ToInt32(MBDataTable[12].ob); } set { MBDataTable[12].ob = value; } }
        public static Int16 gPwmF2 { get { return (Int16)Convert.ToInt32(MBDataTable[13].ob); } set { MBDataTable[13].ob = value; } }
        public static Int16 gPwmF3 { get { return (Int16)Convert.ToInt32(MBDataTable[14].ob); } set { MBDataTable[14].ob = value; } }
        public static Int16 gPwmF4 { get { return (Int16)Convert.ToInt32(MBDataTable[15].ob); } set { MBDataTable[15].ob = value; } }

        public static float gP
        {
            get
            {
                int tmp = (Convert.ToInt32(MBDataTable[16].ob) & 0xFFFF) | ((Convert.ToInt32(MBDataTable[17].ob) & 0xFFFF) << 16);
                byte[] arr = BitConverter.GetBytes(tmp);
                return BitConverter.ToSingle(arr, 0);
            }
            set
            {
                byte[] val = BitConverter.GetBytes(value);
                MBDataTable[16].ob = BitConverter.ToUInt16(val, 0);
                MBDataTable[17].ob = BitConverter.ToUInt16(val, 2);
            }
        }

        public static float gI
        {
            get
            {
                int tmp = (Convert.ToInt32(MBDataTable[18].ob) & 0xFFFF) | ((Convert.ToInt32(MBDataTable[19].ob) & 0xFFFF) << 16);
                byte[] arr = BitConverter.GetBytes(tmp);
                return BitConverter.ToSingle(arr, 0);
            }
            set
            {
                byte[] val = BitConverter.GetBytes(value);
                MBDataTable[18].ob = BitConverter.ToUInt16(val, 0);
                MBDataTable[19].ob = BitConverter.ToUInt16(val, 2);
            }
        }

        public static float gD
        {
            get
            {
                int tmp = (Convert.ToInt32(MBDataTable[20].ob) & 0xFFFF) | ((Convert.ToInt32(MBDataTable[21].ob) & 0xFFFF) << 16);
                byte[] arr = BitConverter.GetBytes(tmp);
                return BitConverter.ToSingle(arr, 0);
            }
            set
            {
                byte[] val = BitConverter.GetBytes(value);
                MBDataTable[20].ob = BitConverter.ToUInt16(val, 0);
                MBDataTable[21].ob = BitConverter.ToUInt16(val, 2);
            }
        }

        public static UInt16 gNode = 100;
        public static UInt16 gBaud = 38400;

        /// <summary>
        /// 获取寄存器或线圈首地址，判断获取寄存器位数
        /// </summary>
        /// <param name="addr">首地址</param>
        /// <returns>成员各数</returns>
        private static int GetAddressValueLength(int addr)
        {
            int size = 0;
            switch (addr)
            {
                case D_DIO: size = 6; break;
                case D_BASE: size = 4; break;
                case D_RANGE: size = 2; break;
                case D_PWM: size = 4; break;
                case D_PID: size = 6; break;
                default: break;
            }
            return size;
        }

        /// <summary>
        /// 根据线圈或者寄存器的首地址、查询指令Function来获取地址所对应的数据类型
        /// </summary>
        /// <param name="addr">寄存器地址</param>
        /// <param name="func">类型</param>
        /// <returns>获取到的数据</returns>
        private static object GetAddressValue(int addr, byte func)
        {
            switch (func)       //功能码类型判断
            {
                case MB_READ_COILS:
                case MB_READ_DISCRETE:
                case MB_READ_HOLD_REG:
                case MB_READ_INPUT_REG: break;
                case MB_WRITE_SINGLE_COIL:
                case MB_WRITE_MULTIPLE_COILS: func = MB_READ_DISCRETE; break;
                case MB_WRITE_SINGLE_REG:
                case MB_WRITE_MULTIPLE_REGS: func = MB_READ_HOLD_REG; break;
                default: return null;
            }

            for (int i = 0; i < MBDataTable.Length; i++)
            {
                if (MBDataTable[i].addr == addr)
                {
                    if (MBDataTable[i].type == func)
                    {
                        return MBDataTable[i].ob;
                    }
                }
            }
            return null;
        }

        /// <summary>
        /// 设置地址所对应的数据
        /// </summary>
        /// <param name="addr">地址</param>
        /// <param name="func">类型</param>
        /// <param name="data">数据</param>
        /// <returns>是否成功</returns>
        private static object SetAddressValue(int addr, byte func, object data)
        {
            for (int i = 0; i < MBDataTable.Length; i++)
            {
                if (MBDataTable[i].addr == addr)
                {
                    if (MBDataTable[i].type == func)
                    {
                        MBDataTable[i].ob = data;
                        return true;
                    }
                }
            }
            return null;
        }

        /// <summary>
        /// 获取一连串数据
        /// </summary>
        /// <param name="addr">首地址</param>
        /// <param name="type">功能码</param>
        /// <param name="len">长度</param>
        /// <returns>转换后的字节数组</returns>
        private static byte[] GetAddressValues(int addr, byte type, int len)
        {
            byte[] arr = null;
            object obj;
            byte temp;
            int temp2;

            switch (type)
            {
                case MB_WRITE_MULTIPLE_COILS:
                    arr = new byte[(len % 8 == 0) ? (len / 8) : (len / 8 + 1)];
                    for (int i = 0; i < arr.Length; i++)
                    {
                        for (int j = 0; j < 8; j++)
                        {   //获取地址所对应的数据 并判断所读数据 是否被指定，有没被指定的数据 直接返回null
                            obj = GetAddressValue(addr + i * 8 + j, MB_READ_COILS);
                            if (obj == null)
                                return null;
                            else
                                temp = Convert.ToByte(obj);
                            arr[i] |= (byte)((temp == 0 ? 0 : 1) << j);
                        }
                    }
                    break;
                case MB_WRITE_MULTIPLE_REGS:
                    arr = new byte[len * 2];
                    for (int i = 0; i < len; i++)
                    {
                        obj = GetAddressValue(addr + i, MB_READ_HOLD_REG);
                        if (obj == null)
                            return null;
                        else
                            temp2 = Convert.ToInt32(obj);
                        arr[i * 2] = (byte)(temp2 >> 8);
                        arr[i * 2 + 1] = (byte)(temp2 & 0xFF);
                    }
                    break;
                default: break;
            }
            return arr;
        }

        #endregion

        #region 校验

        private static readonly byte[] aucCRCHi = {
            0x00, 0xC1, 0x81, 0x40, 0x01, 0xC0, 0x80, 0x41, 0x01, 0xC0, 0x80, 0x41,
            0x00, 0xC1, 0x81, 0x40, 0x01, 0xC0, 0x80, 0x41, 0x00, 0xC1, 0x81, 0x40,
            0x00, 0xC1, 0x81, 0x40, 0x01, 0xC0, 0x80, 0x41, 0x01, 0xC0, 0x80, 0x41,
            0x00, 0xC1, 0x81, 0x40, 0x00, 0xC1, 0x81, 0x40, 0x01, 0xC0, 0x80, 0x41,
            0x00, 0xC1, 0x81, 0x40, 0x01, 0xC0, 0x80, 0x41, 0x01, 0xC0, 0x80, 0x41,
            0x00, 0xC1, 0x81, 0x40, 0x01, 0xC0, 0x80, 0x41, 0x00, 0xC1, 0x81, 0x40,
            0x00, 0xC1, 0x81, 0x40, 0x01, 0xC0, 0x80, 0x41, 0x00, 0xC1, 0x81, 0x40,
            0x01, 0xC0, 0x80, 0x41, 0x01, 0xC0, 0x80, 0x41, 0x00, 0xC1, 0x81, 0x40,
            0x00, 0xC1, 0x81, 0x40, 0x01, 0xC0, 0x80, 0x41, 0x01, 0xC0, 0x80, 0x41,
            0x00, 0xC1, 0x81, 0x40, 0x01, 0xC0, 0x80, 0x41, 0x00, 0xC1, 0x81, 0x40,
            0x00, 0xC1, 0x81, 0x40, 0x01, 0xC0, 0x80, 0x41, 0x01, 0xC0, 0x80, 0x41,
            0x00, 0xC1, 0x81, 0x40, 0x00, 0xC1, 0x81, 0x40, 0x01, 0xC0, 0x80, 0x41,
            0x00, 0xC1, 0x81, 0x40, 0x01, 0xC0, 0x80, 0x41, 0x01, 0xC0, 0x80, 0x41,
            0x00, 0xC1, 0x81, 0x40, 0x00, 0xC1, 0x81, 0x40, 0x01, 0xC0, 0x80, 0x41,
            0x01, 0xC0, 0x80, 0x41, 0x00, 0xC1, 0x81, 0x40, 0x01, 0xC0, 0x80, 0x41,
            0x00, 0xC1, 0x81, 0x40, 0x00, 0xC1, 0x81, 0x40, 0x01, 0xC0, 0x80, 0x41,
            0x00, 0xC1, 0x81, 0x40, 0x01, 0xC0, 0x80, 0x41, 0x01, 0xC0, 0x80, 0x41,
            0x00, 0xC1, 0x81, 0x40, 0x01, 0xC0, 0x80, 0x41, 0x00, 0xC1, 0x81, 0x40,
            0x00, 0xC1, 0x81, 0x40, 0x01, 0xC0, 0x80, 0x41, 0x01, 0xC0, 0x80, 0x41,
            0x00, 0xC1, 0x81, 0x40, 0x00, 0xC1, 0x81, 0x40, 0x01, 0xC0, 0x80, 0x41,
            0x00, 0xC1, 0x81, 0x40, 0x01, 0xC0, 0x80, 0x41, 0x01, 0xC0, 0x80, 0x41,
            0x00, 0xC1, 0x81, 0x40
        };
        private static readonly byte[] aucCRCLo = {
            0x00, 0xC0, 0xC1, 0x01, 0xC3, 0x03, 0x02, 0xC2, 0xC6, 0x06, 0x07, 0xC7,
            0x05, 0xC5, 0xC4, 0x04, 0xCC, 0x0C, 0x0D, 0xCD, 0x0F, 0xCF, 0xCE, 0x0E,
            0x0A, 0xCA, 0xCB, 0x0B, 0xC9, 0x09, 0x08, 0xC8, 0xD8, 0x18, 0x19, 0xD9,
            0x1B, 0xDB, 0xDA, 0x1A, 0x1E, 0xDE, 0xDF, 0x1F, 0xDD, 0x1D, 0x1C, 0xDC,
            0x14, 0xD4, 0xD5, 0x15, 0xD7, 0x17, 0x16, 0xD6, 0xD2, 0x12, 0x13, 0xD3,
            0x11, 0xD1, 0xD0, 0x10, 0xF0, 0x30, 0x31, 0xF1, 0x33, 0xF3, 0xF2, 0x32,
            0x36, 0xF6, 0xF7, 0x37, 0xF5, 0x35, 0x34, 0xF4, 0x3C, 0xFC, 0xFD, 0x3D,
            0xFF, 0x3F, 0x3E, 0xFE, 0xFA, 0x3A, 0x3B, 0xFB, 0x39, 0xF9, 0xF8, 0x38,
            0x28, 0xE8, 0xE9, 0x29, 0xEB, 0x2B, 0x2A, 0xEA, 0xEE, 0x2E, 0x2F, 0xEF,
            0x2D, 0xED, 0xEC, 0x2C, 0xE4, 0x24, 0x25, 0xE5, 0x27, 0xE7, 0xE6, 0x26,
            0x22, 0xE2, 0xE3, 0x23, 0xE1, 0x21, 0x20, 0xE0, 0xA0, 0x60, 0x61, 0xA1,
            0x63, 0xA3, 0xA2, 0x62, 0x66, 0xA6, 0xA7, 0x67, 0xA5, 0x65, 0x64, 0xA4,
            0x6C, 0xAC, 0xAD, 0x6D, 0xAF, 0x6F, 0x6E, 0xAE, 0xAA, 0x6A, 0x6B, 0xAB,
            0x69, 0xA9, 0xA8, 0x68, 0x78, 0xB8, 0xB9, 0x79, 0xBB, 0x7B, 0x7A, 0xBA,
            0xBE, 0x7E, 0x7F, 0xBF, 0x7D, 0xBD, 0xBC, 0x7C, 0xB4, 0x74, 0x75, 0xB5,
            0x77, 0xB7, 0xB6, 0x76, 0x72, 0xB2, 0xB3, 0x73, 0xB1, 0x71, 0x70, 0xB0,
            0x50, 0x90, 0x91, 0x51, 0x93, 0x53, 0x52, 0x92, 0x96, 0x56, 0x57, 0x97,
            0x55, 0x95, 0x94, 0x54, 0x9C, 0x5C, 0x5D, 0x9D, 0x5F, 0x9F, 0x9E, 0x5E,
            0x5A, 0x9A, 0x9B, 0x5B, 0x99, 0x59, 0x58, 0x98, 0x88, 0x48, 0x49, 0x89,
            0x4B, 0x8B, 0x8A, 0x4A, 0x4E, 0x8E, 0x8F, 0x4F, 0x8D, 0x4D, 0x4C, 0x8C,
            0x44, 0x84, 0x85, 0x45, 0x87, 0x47, 0x46, 0x86, 0x82, 0x42, 0x43, 0x83,
            0x41, 0x81, 0x80, 0x40
        };
        /// <summary>
        /// CRC效验
        /// </summary>
        /// <param name="pucFrame">效验数据</param>
        /// <param name="usLen">数据长度</param>
        /// <returns>效验结果</returns>
        public static int Crc16(byte[] pucFrame, int usLen)
        {
            int i = 0;
            byte ucCRCHi = 0xFF;
            byte ucCRCLo = 0xFF;
            UInt16 iIndex = 0x0000;

            while (usLen-- > 0)
            {
                iIndex = (UInt16)(ucCRCLo ^ pucFrame[i++]);
                ucCRCLo = (byte)(ucCRCHi ^ aucCRCHi[iIndex]);
                ucCRCHi = aucCRCLo[iIndex];
            }
            return (ucCRCHi << 8 | ucCRCLo);
        }

        #endregion

        #region 发送指命操作 Query

        /*
         * ModBus 报文模型
         * ----------<--------ADU:应用数据单元------------>---------
         *           数据域  |  功能码  |  数据  |  差错校验
         * ------------------<-PDU:协议数据单元->-------------------
         * 
        */

        /// <summary>
        /// 首部分数据 node:节点
        /// </summary>
        /// <param name="node">Slave Address</param>
        /// <param name="addr">Register Starting Address Hi,Lo</param>
        /// <param name="len">数据长度，或单个数据</param>
        /// <param name="stat"></param>
        /// <returns></returns>
        private static byte[] SendTrainHead(int node, int addr, int len, byte stat)
        {
            byte[] head = new byte[6];

            head[0] = Convert.ToByte(node);
            head[1] = stat;
            head[2] = (byte)(addr >> 8);//Register starting address Hi
            head[3] = (byte)(addr & 0xFF);//Register starting address Lo
            head[4] = (byte)(len >> 8);//No.Points Hi
            head[5] = (byte)(len & 0xFF);//No.Roints Lo

            return head;
        }

        /// <summary>
        /// 计算数据长度 并在0x0f,0x10功能下 加载字节数
        /// </summary>
        /// <param name="arr"></param>
        /// <param name="len">如果是操作多个线圈或者寄存器，则修改len；否则len=0</param>
        /// <param name="stat"></param>
        /// <returns></returns>
        private static byte[] SendTrainBytes(byte[] arr, ref int len, byte stat)
        {
            byte[] res;
            switch (stat)
            {
                default: len = 0; break;

                case MB_READ_COILS:
                case MB_READ_DISCRETE:
                case MB_READ_HOLD_REG:
                case MB_READ_INPUT_REG:
                case MB_WRITE_SINGLE_COIL:
                case MB_WRITE_SINGLE_REG:
                    len = 0;
                    break;

                case MB_WRITE_MULTIPLE_COILS://如果Function是0FH(强制多个线圈命令),则多加Byte Count 位 
                    len = (len % 8 == 0) ? (len / 8) : (len / 8 + 1);
                    res = new byte[arr.Length + 1];
                    arr.CopyTo(res, 0);
                    res[arr.Length] = (byte)(len);//设置Byte Count
                    arr = res;
                    break;

                case MB_WRITE_MULTIPLE_REGS://如果Function是10H(预置多个寄存器),则多加Byte Count 位 
                    len *= 2;
                    res = new byte[arr.Length + 1];
                    arr.CopyTo(res, 0);
                    res[arr.Length] = (byte)len;      //把字节写入数据最后位置
                    arr = res;
                    break;

            }
            return arr;
        }

        /// <summary>
        /// 主控方式  发送指令模板
        /// </summary>
        /// <param name="node">节点Slave Address</param>
        /// <param name="data">数据</param>
        /// <param name="addr">地址Register starting address Hi,Lo</param>
        /// <param name="con">查询线圈或者寄存器的个数</param>
        /// <param name="stat">功能码Function</param>
        /// <returns></returns>
        private static byte[] SendTrainCyclostyle(int node, byte[] data, int addr, int con, byte func)
        {
            int crcVal = 0;
            byte[] headData = SendTrainHead(node, addr, con, func);                   //写首部分数据
            byte[] headDataLen = SendTrainBytes(headData, ref con, func);       //计算数据的长度，有字节则写入。
            byte[] res = new byte[headDataLen.Length + con + 2];

            headDataLen.CopyTo(res, 0);

            if ((func == MB_WRITE_MULTIPLE_REGS) || (func == MB_WRITE_MULTIPLE_COILS))
                Array.Copy(data, 0, res, headDataLen.Length, con); //从Byte Count位开始把需要强制的线圈位或者需要预置的寄存器位添加到数据帧中

            crcVal = Crc16(res, res.Length - 2);//校验数据
            res[res.Length - 2] = (byte)(crcVal & 0xFF);
            res[res.Length - 1] = (byte)(crcVal >> 8);

            return res;//写好完整数据帧
        }

        /// <summary>
        /// 封装好完整的发送数据帧
        /// </summary>
        /// <param name="node">从机地址</param>
        /// <param name="cmd">指令信息</param>
        /// <returns></returns>
        private static byte[] SendPduPack(int node, MBCmd cmd)
        {
            byte[] res = null;
            switch (cmd.func)
            {
                case MB_READ_COILS:
                case MB_READ_DISCRETE:
                case MB_READ_HOLD_REG:
                case MB_READ_INPUT_REG:
                case MB_WRITE_SINGLE_COIL:
                case MB_WRITE_SINGLE_REG:
                    res = SendTrainCyclostyle(node, null, cmd.addr, cmd.len, (byte)cmd.func); break;

                case MB_WRITE_MULTIPLE_COILS:
                case MB_WRITE_MULTIPLE_REGS:
                    byte[] data = GetAddressValues(cmd.addr, (byte)cmd.func, cmd.len);
                    res = SendTrainCyclostyle(node, data, cmd.addr, cmd.len, (byte)cmd.func); break;
            }
            return res;
        }
        #endregion

        #region 回传数据操作 Response

        /// <summary>
        /// 存储回传的线圈
        /// </summary>
        /// <param name="data">回传的数组</param>
        /// <param name="addr">首地址</param>
        /// <returns>存储是否正确</returns>
        private static bool ReadDiscrete(byte[] data, int addr)
        {
            bool res = true;
            //Response中的data[1]是读取寄存器或者线圈的个数Byte Count
            //data[1]是从机首地址Slave Address
            int len = data[2];

            if (len != (data.Length - 5))  //数据长度不正确 直接返回错误
                return false;

            for (int i = 0; i < len; i++)//判断读取的数据是否为空
            {
                for (int j = 0; j < 8; j++)
                {
                    if (SetAddressValue(addr + i * 8 + j, data[1], data[i + 3] & (0x01 << j)) == null)
                    {
                        return false;
                    }
                }
            }
            return res;
        }

        /// <summary>
        /// 读回传的寄存器
        /// </summary>
        /// <param name="data">回传的数组</param>
        /// <param name="addr">首地址</param>
        /// <returns>存储是否正确</returns>
        private static bool ReadReg(byte[] data, int addr)
        {
            bool res = true;
            int len = data[2];

            if (len != (data.Length - 5))  //数据长度不正确 直接退出
                return false;

            for (int i = 0; i < len; i += 2)
            {
                if (SetAddressValue(addr + i / 2, data[1], (data[i + 3] << 8) | data[i + 4]) == null)
                {
                    res = false;
                    break;
                }
            }
            return res;
        }

        /// <summary>
        /// 回传的数据处理
        /// </summary>
        /// <param name="buff">回传的整帧数据</param>
        /// <param name="addr">当前所操作的首地址</param>
        /// <returns></returns>
        private static bool ReceiveDataProcess(byte[] buff, int addr)
        {
            if (buff == null)
                return false;
            if (buff.Length < 5)    //回传的数据 地址+功能码+长度+2效验 = 5字节
                return false;

            bool res = true;
            switch (buff[1])//判断读取的Function，是否读取成功
            {
                case MB_READ_COILS: ReadDiscrete(buff, addr); break;
                case MB_READ_DISCRETE: ReadDiscrete(buff, addr); break;
                case MB_READ_HOLD_REG: ReadReg(buff, addr); break;
                case MB_READ_INPUT_REG: ReadReg(buff, addr); break;
                case MB_WRITE_SINGLE_COIL:
                case MB_WRITE_SINGLE_REG:
                case MB_WRITE_MULTIPLE_COILS:
                case MB_WRITE_MULTIPLE_REGS: break;
                default: res = false; break;
            }
            return res;
        }

        #endregion

        #region 收发调度

        /// <summary>
        /// 添加重复操作指令
        /// </summary>
        /// <param name="sci">待发送的指命管道</param>
        /// <param name="addr">所添加指令的首地址</param>
        /// <param name="len">所添加指令的寄存器或线圈个数</param>
        /// <param name="func">所添加指令的功能码</param>
        private static void SciAddRepeatCmd(ref MBSci sci, int addr, int len, int func)
        {
            if (sci.rtCount >= MB_SCI_MAX_COUNT - 1)  //超出指令管道最大长度 直接退出
                return;
            if (len == 0)                               //地址的数据长度为空 直接退出
                return;

            sci.cmd[sci.rtCount].addr = addr;
            sci.cmd[sci.rtCount].len = len;
            sci.cmd[sci.rtCount].func = func;
            sci.cmd[sci.rtCount].res = 0;
            sci.rtCount++;
        }

        /// <summary>
        /// 添加一次性操作指令
        /// </summary>
        /// <param name="sci">待发送的指命管道</param>
        /// <param name="addr">所添加指令的首地址</param>
        /// <param name="len">所添加指令的寄存器或线圈个数</param>
        /// <param name="stat">所添加指令的功能码</param>
        private static void SciAddCmd(ref MBSci sci, int addr, int len, int stat)
        {
            if (len == 0)                               //地址的数据长度为空 直接退出
                return;

            for (int i = sci.rtCount; i < MB_SCI_MAX_COUNT; i++)
            {
                if (sci.cmd[i].addr == -1)      //把指令载入到空的管道指令上
                {
                    sci.cmd[i].addr = addr;
                    sci.cmd[i].len = len;
                    sci.cmd[i].func = stat;
                    sci.cmd[i].res = 0;
                    break;
                }
            }
        }

        /// <summary>
        /// 清空重复读取指令集
        /// </summary>
        /// <param name="sci">待发送的指命管道</param>
        private static void SciClearRepeatCmd(ref MBSci sci)
        {
            sci.rtCount = 0;
        }

        /// <summary>
        /// 清空一次性读取指令集
        /// </summary>
        /// <param name="sci">待发送的指命管道</param>
        private static void SciClearCmd(ref MBSci sci)
        {
            for (int i = sci.rtCount; i < MB_SCI_MAX_COUNT; i++)
            {
                sci.cmd[i].addr = -1;
                sci.cmd[i].len = 0;
                sci.cmd[i].res = 0;
            }
        }

        /// <summary>
        /// 跳到下一个操作指令
        /// </summary>
        /// <param name="sci">待发送的指命管道</param>
        private static void SciJumbNext(ref MBSci sci)
        {
            if (sci.index >= sci.rtCount)           //非实时读取地址会被清除
            {
                sci.cmd[sci.index].addr = -1;
                sci.cmd[sci.index].len = 0;
                sci.cmd[sci.index].func = 0;
            }

            do
            {
                sci.index++;
                if (sci.index >= MB_SCI_MAX_COUNT)    //超出指令最大范围
                {
                    sci.index = 0;
                    if (sci.rtCount == 0)               //如果固定实时读取 为空 直接跳出
                        break;
                }

            } while (sci.cmd[sci.index].addr == -1);
            sci.cmd[sci.index].res = 0;             //本次返回状态清零
        }

        /// <summary>
        /// 发送指令调度锁定
        /// </summary>
        public static void SciSchedulingLock()
        {
            sciLock = true;
        }
        /// <summary>
        /// 发送指令调度解锁
        /// </summary>
        public static void SciSchedulingUnlock()
        {
            sciLock = false;
        }

        /// <summary>
        /// 待发送的指令管道调度
        /// </summary>
        /// <param name="sci">待发送的指命管道</param>
        /// <param name="rBuf">收到正确的回传数据</param>
        /// <param name="wBuf">准备发送的指令数据</param>
        private static void SciScheduling(ref MBSci sci, ref byte[] rBuf, ref byte[] wBuf)
        {
            if (sciLock)   //如果被加锁 直接退出 
                return;

            if (sci.cmd[0].addr == -1)
                return;

            if ((sci.cmd[sci.index].res != 0) || (sci.count >= sci.maxRepeatCount))
            {
                sci.count = 0;       //发送次数清零
                if (sci.cmd[sci.index].res != 0)    //如果收到了正常返回
                {
                    ReceiveDataProcess(rBuf, sci.cmd[sci.index].addr);     //保存数据
                    rBuf = null;        //清空当前接收缓冲区的内容， 以防下次重复读取
                }
                else
                {
                    //参数操作失败
                }

                SciJumbNext(ref sci);
            }
            wBuf = SendPduPack((int)gNode, sci.cmd[sci.index]);     //发送指令操作
            sci.count++;                            //发送次数加1
        }

        /// <summary>
        /// 快速刷新 处理接收到的数据   建议:10ms以下
        /// </summary>
        /// <returns>所正确回传数据的功能码, null:回传不正确</returns>
        private static int MBQuickRefresh()
        {
            int res = -1;
            if (rBuff != null)
            {
                SciSchedulingLock();
                if (ReceiveDataProcess(rBuff, gMBSci.cmd[gMBSci.index].addr) == true)
                {
                    gMBSci.cmd[gMBSci.index].res = 1;   //标记 所接收到的数据正确
                    res = gMBSci.cmd[gMBSci.index].func;
                }
                rBuff = null;
                SciSchedulingUnlock();
            }
            return res;
        }

        /// <summary>
        /// 调度间隔时间刷新        建议:50ms以上
        /// </summary>
        /// <returns>封装好的协议帧</returns>
        private static void MBSchedRefresh()
        {
            SciScheduling(ref gMBSci, ref rBuff, ref wBuff);
            if (wBuff != null)
                comm.Write(wBuff, 0, wBuff.Length);
        }

        #endregion

        #region 接口函数

        /// <summary>
        /// 清空存放一次性的指令空间
        /// </summary>
        public static void MBClearCmd()
        {
            SciClearCmd(ref gMBSci);
        }

        /// <summary>
        /// 添加固定刷新（重复） 操作指令
        /// </summary>
        /// <param name="addr">寄存器或线圈的地址</param>
        /// <param name="func">功能码</param>
        public static void MBAddRepeatCmd(int addr, byte func)
        {
            for (int i = 0; i < GetAddressValueLength(addr); i++)
                if (GetAddressValue(addr, func) == null)        //如果所添加的指令没有在MODBUS对应表中定义 直接退出
                    return;
            SciAddRepeatCmd(ref gMBSci, addr, GetAddressValueLength(addr), func);
        }

        /// <summary>
        /// 添加一次性 操作指令
        /// </summary>
        /// <param name="addr">寄存器或线圈的地址</param>
        /// <param name="func">功能码</param>
        public static void MBAddCmd(int addr, byte func)
        {
            for (int i = 0; i < GetAddressValueLength(addr); i++)
                if (GetAddressValue(addr, func) == null)        //如果所添加的指令没有在MODBUS对应表中定义 直接退出
                    return;
            SciAddCmd(ref gMBSci, addr, GetAddressValueLength(addr), func);
        }

        /// <summary>
        /// 串口参数配置
        /// </summary>
        /// <param name="commx">所用到的串口</param>
        /// <param name="node"></param>
        /// <param name="baud"></param>
        public static void MBConfig(SerialPort commx, UInt16 node, UInt16 baud)
        {
            gBaud = baud;
            gNode = node;
            comm = commx;
            SciClearRepeatCmd(ref gMBSci);
            SciClearCmd(ref gMBSci);
        }

        /// <summary>
        /// 读取串口中接收到的数据
        /// </summary>
        /// <param name="comm">所用到的串口</param>
        public static void MBDataReceive()
        {
            if (comm == null)                       //如果串口没有被初始化直接退出
                return;
            SciSchedulingLock();
            System.Threading.Thread.Sleep(20);      //等待缓冲器满

            buffLen = comm.BytesToRead;          //获取缓冲区字节长度
            if (buffLen > MB_MAX_LENGTH)            //如果长度超出范围 直接退出
            {
                SciSchedulingUnlock();
                return;
            }
            comm.Read(buff, 0, buffLen);            //读取数据
            if (gMBSci.cmd[gMBSci.index].func == buff[1])
            {
                if (Crc16(buff, buffLen) == 0)
                {
                    rBuff = new byte[buffLen];
                    Array.Copy(buff, rBuff, buffLen);
                }
            }
            SciSchedulingUnlock();
        }

        /// <summary>
        /// MODBUS的实时刷新任务，在定时器在实时调用此函数
        /// 指令发送间隔时间等于实时器乘以10。 例：定时器5ms调用一次  指令发送间隔为50ms。
        /// </summary>
        /// <returns>返回当前功能读取指令回传 的功能码</returns>
        public static int MBRefresh()
        {
            if (sciLock)   //如果被加锁 直接退出 
                return 0;

            mbRefreshTime++;
            if (mbRefreshTime > 10)
            {
                mbRefreshTime = 0;
                MBSchedRefresh();
            }
            return MBQuickRefresh();
        }
        #endregion


    }

}
