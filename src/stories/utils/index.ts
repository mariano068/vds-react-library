
export const convert = (str: string) => str.replaceAll('<', '&#x3C;')

export const htmlToText = (html: any) => {
  const temp = document.createElement('div');
  temp.innerHTML = html;
  return temp.textContent;
}
