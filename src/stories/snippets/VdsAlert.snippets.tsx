import * as React from 'react'
import { VdsAlert } from '../../vds/VdsAlert/VdsAlert'
import { convert } from '../utils'

//#region Info alert
export const alert_info_example_snippet = convert(`
import React from 'react';
import { VdsAlert } from 'vds-components';

export default () => {

    return (
      <VdsAlert severity="info">
        Lorem ipsum dolor sit amlet, consectetur adipiscing elit.
      </VdsAlert>
    );
}
`);
export const Alert_Info_Example = () => {

  return (
    <VdsAlert severity="info">
      Lorem ipsum dolor sit amlet, consectetur adipiscing elit.
    </VdsAlert>
  )
}
//#endregion

//#region Success alert
export const alert_success_example_snippet = convert(`
import React from 'react';
import { VdsAlert } from 'vds-components';

export default () => {

    return (
      <VdsAlert severity="success">
        Lorem ipsum dolor sit amlet, consectetur adipiscing elit.
      </VdsAlert>
    );
}
`);
export const Alert_Success_Example = () => {

  return (
    <VdsAlert severity="success">
      Lorem ipsum dolor sit amlet, consectetur adipiscing elit.
    </VdsAlert>
  )
}
//#endregion

//#region Warning alert
export const alert_warning_example_snippet = convert(`
import React from 'react';
import { VdsAlert } from 'vds-components';

export default () => {

    return (
      <VdsAlert severity="warning">
        Lorem ipsum dolor sit amlet, consectetur adipiscing elit.
      </VdsAlert>
    );
}
`);
export const Alert_Warning_Example = () => {

  return (
    <VdsAlert severity="warning">
      Lorem ipsum dolor sit amlet, consectetur adipiscing elit.
    </VdsAlert>
  )
}
//#endregion

//#region error alert
export const alert_error_example_snippet = convert(`
import React from 'react';
import { VdsAlert } from 'vds-components';

export default () => {

    return (
      <VdsAlert severity="error">
        Lorem ipsum dolor sit amlet, consectetur adipiscing elit.
      </VdsAlert>
    );
}
`);
export const Alert_Error_Example = () => {

  return (
    <VdsAlert severity="error">
      Lorem ipsum dolor sit amlet, consectetur adipiscing elit.
    </VdsAlert>
  )
}
//#endregion
