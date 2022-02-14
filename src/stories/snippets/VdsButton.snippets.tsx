import { Grid } from '@mui/material'
import * as React from 'react'
import { VdsButton } from '../../vds/VdsButton/VdsButton'
import { convert } from '../utils'

//#region Primary button
export const primary_contained_button_example_snippet = convert(`
import React from 'react';
import { Breadcrumb } from 'vds-components';

export default () => {

    const onClickHandler: React.MouseEventHandler<HTMLAnchorElement> = (ev) => console.dir(ev);

    return (
        <VdsButton color="primary" variant="contained" onClick={onClickHandler}>
          Primary Button
        </VdsButton>
    );
}
`)
export const Primary_Contained_Button_Example_Snippet = () => {

  return (
    <Grid container spacing={2}>
      <Grid item lg={6}>
        <VdsButton color="primary" variant="contained">
          Primary Button
        </VdsButton>
        <div>
          <h4>Standard</h4>
          <h6>To use on light background</h6>
        </div>
      </Grid>
      <Grid item lg={6}>
        <VdsButton color="primary" variant="contained" disabled>
          Primary Button
        </VdsButton>
        <div>
          <h4>Disabled</h4>
          <h6>To use on light background</h6>
        </div>
      </Grid>
    </Grid>
  )
}
//#endregion

//#region Secondary button
export const primary_outlined_button_example_snippet = convert(`
import React from 'react';
import { VdsButton } from 'vds-components';

export default () => {

    const onClickHandler: React.MouseEventHandler<HTMLAnchorElement> = (ev) => console.dir(ev);

    return (
        <VdsButton color="primary" variant="outlined" onClick={onClickHandler}>
          Primary Button
        </VdsButton>
    );
}
`)
export const Primary_Outlined_Button_Example_Snippet = () => {

  return (
    <Grid container spacing={2}>
      <Grid item lg={6}>
        <VdsButton color="primary" variant="outlined">
          Primary Outlined Button
        </VdsButton>
        <div>
          <h4>Standard</h4>
          <h6>To use on light background</h6>
        </div>
      </Grid>
      <Grid item lg={6}>
        <VdsButton color="primary" variant="outlined" disabled>
          Primary Outlined Button
        </VdsButton>
        <div>
          <h4>Disabled</h4>
          <h6>To use on light background</h6>
        </div>
      </Grid>
    </Grid>
  )
}
//#endregion

//#region Secondary button
export const secondary_contained_button_example_snippet = convert(`
import React from 'react';
import { Breadcrumb } from 'vds-components';

export default () => {

    const onClickHandler: React.MouseEventHandler<HTMLAnchorElement> = (ev) => console.dir(ev);

    return (
        <VdsButton color="secondary" variant="contained" onClick={onClickHandler}>
          Primary Button
        </VdsButton>
    );
}
`)
export const Secondary_Contained_Button_Example_Snippet = () => {

  return (
    <Grid container spacing={2}>
      <Grid item lg={6}>
        <VdsButton color="secondary" variant="contained">
          Secondary Contained Button
        </VdsButton>
        <div>
          <h4>Standard</h4>
          <h6>To use on light background</h6>
        </div>
      </Grid>
      <Grid item lg={6}>
        <VdsButton color="secondary" variant="contained" disabled>
          Secondary Contained Button
        </VdsButton>
        <div>
          <h4>Disabled</h4>
          <h6>To use on light background</h6>
        </div>
      </Grid>
    </Grid>
  )
}
//#endregion
