
class LineBreakTransformer {
    constructor() {
      this.container = '';
    }
  
    transform(chunk, controller) {
      this.container += chunk;
      const lines = this.container.split('\r\n');
      this.container = lines.pop();
      lines.forEach(line => controller.enqueue(line));
    }
  
    flush(controller) {
      if (this.container) {
        controller.enqueue(this.container);
      }
    }
  }
  
  async function readSerialContinuously(port) {
    const textDecoder = new TextDecoderStream();
    const readableStreamClosed = port.readable.pipeTo(textDecoder.writable);
    const reader = textDecoder.readable
      .pipeThrough(new TransformStream(new LineBreakTransformer()))
      .getReader();
  
    try {
      while (true) {
        const { value, done } = await reader.read();
        if (done) {
          // The stream has been canceled.
          break;
        }
        // Process the line here
        processLine(value);
      }
    } catch (error) {
      console.error('Error reading serial data:', error);
    } finally {
      reader.releaseLock();
      await readableStreamClosed.catch(() => { /* Ignore the error */ });
    }
  }
  
  function processLine(line) {
    console.log(line)
  }


async function connectToSerialPort() {
  if ("serial" in navigator) {
    console.log("Web Serial API is supported");
  } else {
    console.log("Web Serial API is not supported in this browser");
    return
  }
  try {
    const port = await navigator.serial.requestPort();
    await port.open({ baudRate: 9600 });
    readSerialContinuously(port);
  } catch (error) {
    console.error("Error:", error);
  }
}
const startConnectionButton = document.getElementById("start-connection");
startConnectionButton.addEventListener("click", connectToSerialPort);
